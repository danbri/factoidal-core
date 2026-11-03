/-
Wasm.Ops.LwsDataset — the LWS dataset-view ops
(https://github.com/danbri/factoidal/issues/1011, version 2).

  lwsViewPlan(listDoneJson [, containerIri])
    -> {"ok":true,"containers":[…],"resources":[…],"metadata":[…],
        "skipped":[{resource,reason}]}
    `metadata` is the listed container (the second argument; when it is
    absent or empty, the `id` of the listing document, when it has one),
    then every member that is not a container: the resources whose linkset
    the host reads.
  lwsDatasetView(docsJson)
    docsJson = {"listings":[{"container","done"}],"reads":[{"resource","done"}],
                "linksets":[{"resource","done"}]}
    -> {"ok":true,"nquads":"…","graphs":N,"toc":"<storage description IRI>",
        "evidence":[{"resource","etag","lastModified"} | {"resource","linkset","etag"}],
        "skipped":[{"resource","reason"}]}
    An error when no linkset read of the storage root (the first container
    listed) gives the storage description IRI, the name of the
    table-of-contents graph.

`done` is the `done` document of the LWS client's `list`, `read` or
`readLinkset` (`Wasm/Ops/LwsClient.lean`). Every decision is
`L4Factoidal.LWS.DatasetView` (`planListing`, `readOfDone`, `linksetOfDone`,
`view`); the host is `npm/factoidal/lws/dataset.mjs`.
-/
import Wasm.Ops.Support
import L4Factoidal.LWS.DatasetViewRead

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS.DatasetView

/-- `lwsViewPlan(listDoneJson [, containerIri])`: which members of a listing
to list, read or leave out, and whose linksets to read. -/
def lwsViewPlan (text : String) (container : Option String := none) : String :=
  match parseJson text with
  | .error _ => errJson "lwsViewPlan: the listing is not JSON"
  | .ok j =>
    let c := container.bind (fun s => if s.isEmpty then none else some s)
    match planJson (planListing j c) with
    | .object fs => okWith fs
    | _ => errJson "lwsViewPlan: internal"

/-- `lwsDatasetView(docsJson)`: the dataset view of the listings, reads and
linkset reads, as N-Quads, with the evidence. -/
def lwsDatasetView (text : String) : String :=
  match parseJson text with
  | .error _ => errJson "lwsDatasetView: the documents are not JSON"
  | .ok j => match viewOfDocsJson (docsOfJson j) with
    | .ok (.object fs) => okWith fs
    | .ok _ => errJson "lwsDatasetView: internal"
    | .error e => errJson s!"lwsDatasetView: {e}"

def lwsDatasetOpNames : List String := ["lwsViewPlan", "lwsDatasetView"]

-- A listing: one container, one Turtle resource, one PNG.
#guard (lwsViewPlan "{\"members\":[{\"id\":\"http://s/a/\",\"type\":\"Container\"},{\"id\":\"http://s/b.ttl\",\"type\":\"DataResource\",\"format\":\"text/turtle\"},{\"id\":\"http://s/c.png\",\"type\":\"DataResource\",\"format\":\"image/png\"}]}" (some "http://s/"))
  = "{\"ok\":true,\"containers\":[\"http://s/a/\"],\"resources\":[\"http://s/b.ttl\"],\"metadata\":[\"http://s/\",\"http://s/b.ttl\",\"http://s/c.png\"],\"skipped\":[{\"resource\":\"http://s/c.png\",\"reason\":\"no RDF reader for media type image/png\"}]}"
-- No container argument (or an empty one) and no `id`: the members only.
#guard (lwsViewPlan "{\"members\":[{\"id\":\"http://s/b.ttl\",\"type\":\"DataResource\"}]}" (some ""))
  = "{\"ok\":true,\"containers\":[],\"resources\":[\"http://s/b.ttl\"],\"metadata\":[\"http://s/b.ttl\"],\"skipped\":[]}"
#guard (lwsViewPlan "{}") = "{\"ok\":true,\"containers\":[],\"resources\":[],\"metadata\":[],\"skipped\":[]}"
#guard (lwsViewPlan "not json").startsWith "{\"ok\":false"

/-- A storage root `http://s/` with one Turtle resource, the linkset of the
root (with the storage link) and the linkset of the resource. -/
private def oneResource : String :=
  "{\"listings\":[{\"container\":\"http://s/\",\"done\":{\"members\":[{\"id\":\"http://s/b.ttl\",\"type\":\"DataResource\",\"format\":\"text/turtle\"}]}}]," ++
  "\"reads\":[{\"resource\":\"http://s/b.ttl\",\"done\":{\"status\":200,\"headers\":[[\"content-type\",\"text/turtle\"],[\"etag\",\"\\\"7\\\"\"]],\"body\":\"<> <http://e/p> 1 .\"}}]," ++
  "\"linksets\":[{\"resource\":\"http://s/\",\"done\":{\"url\":\"http://s/?linkset\",\"etag\":\"\\\"r\\\"\",\"linkset\":{\"linkset\":[{\"anchor\":\"http://s/\",\"https://www.w3.org/ns/lws#storage\":[{\"href\":\"http://s/.well-known/lws-storage\"}]}]}}}," ++
  "{\"resource\":\"http://s/b.ttl\",\"done\":{\"url\":\"http://s/b.ttl?linkset\",\"etag\":\"\\\"b\\\"\",\"linkset\":{\"linkset\":[{\"anchor\":\"http://s/b.ttl\",\"up\":[{\"href\":\"http://s/\"}]}]}}}]}"

private def oneView : Option Json := (parseJson (lwsDatasetView oneResource)).toOption

#guard (oneView.bind (·.field? "ok")) = some (.bool true)
#guard (oneView.bind (·.getString? "toc")) = some "http://s/.well-known/lws-storage"
-- the TOC, the document, two linksets
#guard (oneView.bind (·.field? "graphs")) = some (.number "4")
/-- A line of the N-Quads of `oneView`. -/
private def oneLine (l : String) : Bool :=
  (((oneView.bind (·.getString? "nquads")).getD "").splitOn "\n").contains l

-- one linkset graph triple, and the TOC containment and linkset triples
#guard oneLine "<http://s/b.ttl> <http://www.iana.org/assignments/relation/up> <http://s/> <http://s/b.ttl?linkset> ."
#guard oneLine "<http://s/> <https://www.w3.org/ns/lws#items> <http://s/b.ttl> <http://s/.well-known/lws-storage> ."
#guard oneLine "<http://s/b.ttl> <http://www.iana.org/assignments/relation/linkset> <http://s/b.ttl?linkset> <http://s/.well-known/lws-storage> ."
#guard oneLine "<http://s/b.ttl> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/lws#DataResource> <http://s/.well-known/lws-storage> ."
#guard !oneLine "<http://s/> <http://www.w3.org/ns/ldp#contains> <http://s/b.ttl> ."
#guard (oneView.bind (·.getArray? "evidence")) = some
  [ .object [("resource", .string "http://s/b.ttl"), ("etag", .string "\"7\""), ("lastModified", .string "")]
  , .object [("resource", .string "http://s/"), ("linkset", .string "http://s/?linkset"), ("etag", .string "\"r\"")]
  , .object [("resource", .string "http://s/b.ttl"), ("linkset", .string "http://s/b.ttl?linkset"), ("etag", .string "\"b\"")] ]
#guard (oneView.bind (·.getArray? "skipped")) = some []
-- Without a linkset that gives the storage description IRI there is no view.
#guard (lwsDatasetView "{\"reads\":[{\"resource\":\"http://s/c\",\"done\":{\"status\":200,\"headers\":[[\"content-type\",\"text/plain\"]],\"body\":\"x\"}}]}").startsWith
  "{\"ok\":false,\"error\":\"lwsDatasetView: the view needs the storage description IRI"

end L4Wasm.Ops
