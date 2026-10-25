/-
L4Factoidal.LWS.DatasetViewTests — `#guard`s of the LWS dataset view
(https://github.com/danbri/factoidal/issues/1011): a storage of one container
and three Turtle resources, given as the client's `done` documents, read into
a snapshot (`LWS/DatasetViewRead.lean`), and queried through the shipped
evaluator over the LWS source (`Dataflow/LwsSource.lean`). Negative cases: a
non-RDF member is left out of the plan, a read with a non-RDF media type or a
failed status is left out of the snapshot, and a resource change changes the
answers of that graph only.
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

private def member (id type : String) (format : Option String := none) : Json :=
  .object ([("id", .string id), ("type", .string type)] ++
    match format with | some f => [("format", .string f)] | none => [])

private def listing (ms : List Json) : Json := .object [("members", .array ms)]

private def readDone (status : Nat) (ct etag body : String) : Json :=
  .object [ ("status", .number (toString status))
          , ("headers", .array [ .array [.string "Content-Type", .string ct]
                               , .array [.string "ETag", .string etag]
                               , .array [.string "Last-Modified", .string "Thu, 01 Jan 1970 00:00:03 GMT"] ])
          , ("body", .string body) ]

private def rootListing : Json :=
  listing [member (B ++ "notes/") "Container", member (B ++ "c.ttl") "DataResource" "text/turtle"]

private def notesListing : Json :=
  listing [ member (B ++ "notes/a.ttl") "DataResource" "text/turtle"
          , member (B ++ "notes/b.ttl") "DataResource" "text/turtle; charset=utf-8"
          , member (B ++ "notes/pic.png") "DataResource" "image/png" ]

/-! ## The crawl plan -/

#guard (planListing rootListing).containers = [B ++ "notes/"]
#guard (planListing rootListing).resources = [B ++ "c.ttl"]
#guard (planListing notesListing).resources = [B ++ "notes/a.ttl", B ++ "notes/b.ttl"]
-- a member whose media type has no RDF reader is not read
#guard (planListing notesListing).skipped.map (·.1) = [B ++ "notes/pic.png"]
#guard (planListing (listing [])).resources = []

/-! ## The snapshot and its view -/

private def docs : Docs :=
  { listings := [(B, rootListing), (B ++ "notes/", notesListing)]
    reads :=
      [ (B ++ "notes/a.ttl", readDone 200 "text/turtle" "\"1-a\"" "<#it> <http://e/p> \"a\" . _:x <http://e/q> <#it> .")
      , (B ++ "notes/b.ttl", readDone 200 "text/turtle" "\"2-b\"" "<#it> <http://e/p> \"b\" . _:x <http://e/q> <#it> .")
      , (B ++ "c.ttl", readDone 200 "text/turtle" "\"3-c\"" "<> <http://e/p> \"c\" .")
      , (B ++ "notes/pic.png", readDone 200 "image/png" "\"4\"" "PNG")
      , (B ++ "gone.ttl", readDone 404 "text/turtle" "\"5\"" "") ] }

private def snap : Snapshot := (snapshotOfDocs docs).1

#guard snap.resources.map (·.val) = [B ++ "notes/a.ttl", B ++ "notes/b.ttl", B ++ "c.ttl"]
#guard (snapshotOfDocs docs).2.map (·.1) = [B ++ "notes/pic.png", B ++ "gone.ttl"]
#guard (evidenceOf snap).map (fun (r, e, _) => (r, e)) =
  [(B ++ "notes/a.ttl", "\"1-a\""), (B ++ "notes/b.ttl", "\"2-b\""), (B ++ "c.ttl", "\"3-c\"")]
-- every listing member is a containment pair, the PNG included
#guard snap.members.length = 5
#guard (view snap).names.length = 3
-- the relative IRI <#it> resolves against the resource IRI
#guard ((view snap).lookupNamedIri (B ++ "notes/a.ttl")).map (·.length) = some 2

/-! ## Queries over the LWS source -/

/-- The storage the snapshot was read from (the reads are current). -/
private def storage (s : Snapshot) : StorageAt :=
  { current := fun i => (s.reads.find? (fun r => r.resource == i)).map (fun r => (r.etag, r.graph))
    members := s.members }

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

-- GRAPH ?g gives the three resource IRIs, each once
#guard rows? snap "SELECT DISTINCT ?g WHERE { GRAPH ?g { ?s ?p ?o } }" = some 3
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/a.ttl> \{ <{B}notes/a.ttl#it> <http://e/p> \"a\" } }" = some true
#guard ask? snap s!"ASK \{ GRAPH <{B}c.ttl> \{ <{B}c.ttl> <http://e/p> \"c\" } }" = some true
-- the containment graph is the default graph
#guard rows? snap s!"SELECT ?m WHERE \{ <{B}notes/> <http://www.w3.org/ns/ldp#contains> ?m }" = some 3
#guard ask? snap s!"ASK \{ <{B}> <http://www.w3.org/ns/ldp#contains> <{B}notes/> }" = some true
#guard ask? snap s!"ASK \{ GRAPH ?g \{ ?s <http://www.w3.org/ns/ldp#contains> ?m } }" = some false
-- a left-out resource is no graph
#guard ask? snap s!"ASK \{ GRAPH <{B}notes/pic.png> \{ ?s ?p ?o } }" = some false
-- the blank nodes of a.ttl and b.ttl are two nodes (one scope per read)
#guard rows? snap "SELECT DISTINCT ?x WHERE { GRAPH ?g { ?x <http://e/q> ?o } }" = some 2
-- the source rests on one named assumption
#guard ((src snap).assumptions.map (·.name)) = [.lwsReadsAtSnapshot]

/-! ## A resource change changes one graph -/

private def changed : Snapshot := snap.replace ⟨"http://s.example/c.ttl", by decide⟩ "\"9-c\"" []

#guard ask? changed s!"ASK \{ GRAPH <{B}c.ttl> \{ ?s ?p ?o } }" = some false
#guard ask? changed s!"ASK \{ GRAPH <{B}notes/a.ttl> \{ ?s <http://e/p> \"a\" } }" = some true
#guard rows? changed "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }" = some 4
#guard (view changed).names = (view snap).names

end L4Factoidal.LWS.DatasetViewTests
