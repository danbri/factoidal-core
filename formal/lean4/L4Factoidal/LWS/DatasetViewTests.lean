/-
L4Factoidal.LWS.DatasetViewTests — `#guard`s of the LWS dataset view
(https://github.com/danbri/factoidal/issues/1011, version 2): a storage root
with one container, two Turtle resources, one PNG and one resource that
answers 404, with the linkset documents of the root, the container, the
Turtle resources and the PNG in the shape that `LWS/Binding.lean`
`linksetJson` writes (`up`, `type`, `https://www.w3.org/ns/lws#storage`),
given as the client's `done` documents, read into a snapshot
(`LWS/DatasetViewRead.lean`), and queried through the shipped evaluator over
the LWS source (`Dataflow/LwsSource.lean`).

Negative cases: a non-RDF member is not read, a read with a failed status is
left out, a linkset whose IRI is already a graph name is left out with a
reason, a link with no relation IRI or no `href` is left out with a reason,
the view without the storage link is an error, and a document change changes
the graph of that document only.
-/
import L4Factoidal.LWS.DatasetViewRead
import L4Factoidal.Dataflow.LwsSource
import L4Factoidal.Dataflow.EndToEnd

namespace L4Factoidal.LWS.DatasetViewTests

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Dataflow
open L4Factoidal.LWS.DatasetView

private def B : String := "http://s.example/"
private def ST : String := "http://s.example/.well-known/lws-storage"
private def LWSNS : String := "https://www.w3.org/ns/lws#"
private def IANA : String := "http://www.iana.org/assignments/relation/"

private def member (id type : String) (format : Option String := none)
    (extra : List (String × Json) := []) : Json :=
  .object ([("id", .string id), ("type", .string type)] ++
    (match format with | some f => [("format", .string f)] | none => []) ++ extra)

private def listing (ms : List Json) : Json := .object [("members", .array ms)]

private def readDone (status : Nat) (ct etag body : String) : Json :=
  .object [ ("status", .number (toString status))
          , ("headers", .array [ .array [.string "Content-Type", .string ct]
                               , .array [.string "ETag", .string etag]
                               , .array [.string "Last-Modified", .string "Thu, 01 Jan 1970 00:00:03 GMT"] ])
          , ("body", .string body) ]

private def rootListing : Json :=
  listing [ member (B ++ "notes/") "Container"
          , member (B ++ "c.ttl") "DataResource" "text/turtle"
              [("size", .number "24"), ("modified", .string "1970-01-01T00:00:03Z")] ]

private def notesListing : Json :=
  listing [ member (B ++ "notes/a.ttl") "DataResource" "text/turtle; charset=utf-8"
          , member (B ++ "notes/pic.png") "DataResource" "image/png" [("size", .number "3")]
          , member (B ++ "notes/gone.ttl") "DataResource" "text/turtle" ]

/-- A link target array. -/
private def hrefs (ts : List String) : Json := .array (ts.map (fun t => .object [("href", .string t)]))

/-- A `readLinkset` `done` document: `{linkset, url, etag}`. -/
private def linksetDone (url etag : String) (ctx : List (String × Json)) : Json :=
  .object [ ("linkset", .object [("linkset", .array [.object ctx])])
          , ("url", .string url), ("etag", .string etag) ]

private def rootLinkset : Json :=
  linksetDone (B ++ "?linkset") "\"l0\""
    [ ("anchor", .string B), ("type", hrefs [LWSNS ++ "Container"])
    , (LWSNS ++ "storage", hrefs [ST]) ]

private def notesLinkset : Json :=
  linksetDone (B ++ "notes/?linkset") "\"l1\""
    [ ("anchor", .string (B ++ "notes/")), ("up", hrefs [B]), ("type", hrefs [LWSNS ++ "Container"])
    , (LWSNS ++ "storage", hrefs [ST]) ]

-- `Up` is a registered relation type name in upper case; `./` is relative.
private def aLinkset : Json :=
  linksetDone (B ++ "notes/a.ttl?linkset") "\"l2\""
    [ ("anchor", .string (B ++ "notes/a.ttl")), ("Up", hrefs ["./"])
    , ("type", hrefs [LWSNS ++ "DataResource"]), (LWSNS ++ "storage", hrefs [ST]) ]

-- A relative anchor; a relative `describedby` target; a member name that is no
-- relation type; a target object with no `href`.
private def cLinkset : Json :=
  linksetDone (B ++ "c.ttl?linkset") "\"l3\""
    [ ("anchor", .string "c.ttl"), ("up", hrefs [B]), ("describedby", hrefs ["c.ttl.meta"])
    , ("not a rel!", hrefs [B]), ("type", .array [.object [("title", .string "no href")]]) ]

-- No anchor: the link context is the resource IRI.
private def pngLinkset : Json :=
  linksetDone (B ++ "notes/pic.png?linkset") "\"l4\""
    [ ("up", hrefs [B ++ "notes/"]), ("type", hrefs [LWSNS ++ "DataResource"])
    , (LWSNS ++ "storage", hrefs [ST]) ]

-- A linkset served at the IRI of a document (c.ttl): its IRI is already a name.
private def clashLinkset : Json :=
  linksetDone (B ++ "c.ttl") "\"l5\"" [("up", hrefs [B ++ "notes/"])]

/-! ## The crawl plan -/

#guard (planListing rootListing).containers = [B ++ "notes/"]
#guard (planListing rootListing).resources = [B ++ "c.ttl"]
-- no container given and no `id` in the document: the members only
#guard (planListing rootListing).metadata = [B ++ "c.ttl"]
#guard (planListing rootListing (some B)).metadata = [B, B ++ "c.ttl"]
#guard (planListing (.object [("id", .string B), ("members", .array [])])).metadata = [B]
#guard (planListing notesListing).resources = [B ++ "notes/a.ttl", B ++ "notes/gone.ttl"]
-- a member whose media type has no RDF reader is not read, but its linkset is
#guard (planListing notesListing).skipped.map (·.1) = [B ++ "notes/pic.png"]
#guard (planListing notesListing (some (B ++ "notes/"))).metadata =
  [B ++ "notes/", B ++ "notes/a.ttl", B ++ "notes/pic.png", B ++ "notes/gone.ttl"]
#guard (planListing (listing [])).resources = []

/-! ## Relation types -/

#guard (relIri "type").map (·.val) = some "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
#guard (relIri "items").map (·.val) = some "https://www.w3.org/ns/lws#items"
#guard (relIri "Up").map (·.val) = some "http://www.iana.org/assignments/relation/up"
#guard (relIri "linkset").map (·.val) = some "http://www.iana.org/assignments/relation/linkset"
#guard (relIri "https://www.w3.org/ns/lws#storage").map (·.val) = some "https://www.w3.org/ns/lws#storage"
#guard (relIri "not a rel!").isNone
#guard (relIri "").isNone

/-! ## The snapshot and its view -/

private def docs : Docs :=
  { listings := [(B, rootListing), (B ++ "notes/", notesListing)]
    reads :=
      [ (B ++ "notes/a.ttl", readDone 200 "text/turtle" "\"1-a\"" "<#it> <http://e/p> \"a\" . _:x <http://e/q> <#it> .")
      , (B ++ "c.ttl", readDone 200 "text/turtle" "\"3-c\"" "<> <http://e/p> \"c\" . _:x <http://e/q> <> .")
      , (B ++ "notes/gone.ttl", readDone 404 "text/turtle" "\"5\"" "") ]
    linksets :=
      [ (B, rootLinkset), (B ++ "notes/", notesLinkset), (B ++ "notes/a.ttl", aLinkset)
      , (B ++ "c.ttl", cLinkset), (B ++ "notes/pic.png", pngLinkset)
      , (B ++ "notes/gone.ttl", clashLinkset) ] }

private def out : Snapshot × List (String × String) :=
  match snapshotOfDocs docs with
  | .ok v => v
  | .error _ => ({ storage := ⟨"urn:none", by decide⟩, members := [], reads := [] }, [])

private def snap : Snapshot := out.1

-- the name of the table-of-contents graph is the storage description IRI
#guard snap.storage.val = ST
#guard ((view snap).named.head?.map (·.name)) = some (.iri snap.storage)
#guard snap.resources.map (·.val) = [B ++ "notes/a.ttl", B ++ "c.ttl"]
-- the 404 read and the dropped links are left out, with a reason
#guard out.2.map (·.1) = [B ++ "notes/gone.ttl", B ++ "c.ttl", B ++ "c.ttl"]
#guard (evidenceOf snap).map (fun (r, e, _) => (r, e)) =
  [(B ++ "notes/a.ttl", "\"1-a\""), (B ++ "c.ttl", "\"3-c\"")]
#guard (linksetEvidenceOf snap).length = 6
-- names: the TOC, two documents, five linksets; the linkset served at c.ttl is left out
#guard snap.names.map (·.val) =
  [ ST, B ++ "notes/a.ttl", B ++ "c.ttl", B ++ "?linkset", B ++ "notes/?linkset"
  , B ++ "notes/a.ttl?linkset", B ++ "c.ttl?linkset", B ++ "notes/pic.png?linkset" ]
#guard (view snap).names.length = 8
#guard (nameClashes snap).map (·.1) = [B ++ "notes/gone.ttl"]
#guard (view snap).default = []
-- the TOC: 5 containment triples, 12 listing triples, 6 linkset links
#guard snap.toc.length = 23
#guard ((view snap).lookupNamedIri ST).map (·.length) = some 23
-- the relative IRI <#it> resolves against the resource IRI
#guard ((view snap).lookupNamedIri (B ++ "notes/a.ttl")).map (·.length) = some 2

/-! ## Queries over the LWS source -/

/-- The storage the snapshot was read from (the reads are current). -/
private def storage (s : Snapshot) : StorageAt :=
  { storage := s.storage
    current := fun i => (s.reads.find? (fun r => r.resource == i)).map (fun r => (r.etag, r.graph))
    members := s.members
    entries := s.entries
    linksetOf := fun i => (s.linksets.find? (fun l => l.resource == i)).map
      (fun l => (l.linkset, l.etag, l.links)) }

private def src (s : Snapshot) : Sourced := lwsSource (storage s) s

private def rows? (s : Snapshot) (qs : String) : Option Nat :=
  match parseSparql qs none .v11 with
  | .ok q => match shippedEvaluator.run ((src s).input {} q) with
    | .select _ rs => some rs.length
    | _ => none
  | .error _ => none

private def ask? (s : Snapshot) (qs : String) : Option Bool :=
  match parseSparql qs none .v11 with
  | .ok q => match shippedEvaluator.run ((src s).input {} q) with
    | .ask b => some b
    | _ => none
  | .error _ => none

-- GRAPH ?g gives the TOC, the two documents and the five linksets, each once
#guard rows? snap "SELECT DISTINCT ?g WHERE { GRAPH ?g { ?s ?p ?o } }" = some 8
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ ?s ?p ?o } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/a.ttl> \{ <{B}notes/a.ttl#it> <http://e/p> \"a\" } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{B}c.ttl> \{ <{B}c.ttl> <http://e/p> \"c\" } }" = some true
-- the default graph is empty; containment is lws:items in the TOC graph
#guard ask? snap "ASK { ?s ?p ?o }" = some false
#guard rows? snap s!"SELECT ?m WHERE \{ GRAPH <{ST}> \{ <{B}notes/> <{LWSNS}items> ?m } }" = some 3
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ <{B}> <{LWSNS}items> <{B}notes/> } }" = some true
#guard ask? snap "ASK { GRAPH ?g { ?s <http://www.w3.org/ns/ldp#contains> ?m } }" = some false
-- the listing members are typed, with the listing's format, size and modified
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ <{B}notes/> a <{LWSNS}Container> } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ <{B}c.ttl> a <{LWSNS}DataResource> ;
    <http://purl.org/dc/terms/format> \"text/turtle\" ;
    <http://schema.org/size> \"24\"^^<http://www.w3.org/2001/XMLSchema#long> ;
    <http://purl.org/dc/terms/modified> \"1970-01-01T00:00:03Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> } }" = some true
-- the PNG: in the TOC (type, format, size) and with a linkset graph, but no document graph
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ <{B}notes/pic.png> a <{LWSNS}DataResource> ;
    <http://purl.org/dc/terms/format> \"image/png\" ;
    <http://schema.org/size> \"3\"^^<http://www.w3.org/2001/XMLSchema#long> } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/pic.png> \{ ?s ?p ?o } }" = some false
-- no anchor: the link context is the resource IRI
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/pic.png?linkset> \{ <{B}notes/pic.png> <{IANA}up> <{B}notes/> } }" = some true
-- the TOC links each resource to its linkset
#guard ask? snap s!"ASK \{ GRAPH <{ST}> \{ <{B}notes/pic.png> <{IANA}linkset> <{B}notes/pic.png?linkset> } }" = some true
#guard rows? snap s!"SELECT ?r WHERE \{ GRAPH <{ST}> \{ ?r <{IANA}linkset> ?l } }" = some 6
-- `type` is rdf:type; an absolute relation type stays as it is
#guard ask? snap s!"ASK \{ GRAPH <{B}?linkset> \{ <{B}> a <{LWSNS}Container> } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{B}?linkset> \{ <{B}> <{LWSNS}storage> <{ST}> } }" = some true
-- `Up` is the IANA `up`, and the relative href `./` resolves against the linkset IRI
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/a.ttl?linkset> \{ <{B}notes/a.ttl> <{IANA}up> <{B}notes/> } }" = some true
-- a relative anchor and a relative target resolve against the linkset IRI
#guard ask? snap s!"ASK \{ GRAPH <{B}c.ttl?linkset> \{ <{B}c.ttl> <{IANA}describedby> <{B}c.ttl.meta> } }" = some true
-- the links with no relation IRI or no href are not in the graph
#guard ((view snap).lookupNamedIri (B ++ "c.ttl?linkset")).map (·.length) = some 2
-- the linkset served at c.ttl is left out: the graph named c.ttl is the document
#guard ask? snap s!"ASK \{ GRAPH <{B}c.ttl> \{ ?s <{IANA}up> ?o } }" = some false
-- the blank nodes of a.ttl and c.ttl are two nodes (one scope per read)
#guard rows? snap "SELECT DISTINCT ?x WHERE { GRAPH ?g { ?x <http://e/q> ?o } }" = some 2
-- the source rests on one named assumption
#guard ((src snap).assumptions.map (·.name)) = [.lwsReadsAtSnapshot]

/-! ## The JSON output -/

private def json? : Option Json := (viewOfDocsJson docs).toOption

#guard (json?.bind (·.getString? "toc")) = some ST
#guard (json?.bind (·.field? "graphs")) = some (.number "8")
#guard (json?.bind (·.getArray? "evidence")).map (·.length) = some 8
#guard ((json?.bind (·.getArray? "skipped")).getD []).filterMap (·.getString? "resource") =
  [B ++ "notes/gone.ttl", B ++ "c.ttl", B ++ "c.ttl", B ++ "notes/gone.ttl"]

/-! ## Without the storage link there is no view -/

private def docsNoStorage : Docs :=
  { docs with linksets := [(B ++ "notes/a.ttl", aLinkset), (B ++ "notes/", notesLinkset)] }

#guard (snapshotOfDocs docsNoStorage).toOption.isNone
#guard match viewOfDocsJson docsNoStorage with
  | .error e => (e.splitOn "table-of-contents graph").length > 1
  | .ok _ => false
#guard (snapshotOfDocs { docs with listings := [] }).toOption.isNone

/-! ## A document change changes one graph -/

private def changed : Snapshot := snap.replace ⟨"http://s.example/c.ttl", by decide⟩ "\"9-c\"" []

#guard ask? changed s!"ASK \{ GRAPH <{B}c.ttl> \{ ?s ?p ?o } }" = some false
#guard ask? changed s!"ASK \{ GRAPH <{B}notes/a.ttl> \{ ?s <http://e/p> \"a\" } }" = some true
#guard (view changed).names = (view snap).names
#guard (view changed).lookupNamedIri ST = (view snap).lookupNamedIri ST
#guard (view changed).lookupNamedIri (B ++ "c.ttl?linkset") = (view snap).lookupNamedIri (B ++ "c.ttl?linkset")

end L4Factoidal.LWS.DatasetViewTests
