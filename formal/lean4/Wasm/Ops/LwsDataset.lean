/-
Wasm.Ops.LwsDataset — the LWS dataset-view ops
(https://github.com/danbri/factoidal/issues/1011).

  lwsViewPlan(listDoneJson)
    -> {"ok":true,"containers":[…],"resources":[…],"skipped":[{resource,reason}]}
  lwsDatasetView(docsJson)
    docsJson = {"listings":[{"container","done"}],"reads":[{"resource","done"}]}
    -> {"ok":true,"nquads":"…","graphs":N,
        "evidence":[{"resource","etag","lastModified"}],
        "skipped":[{"resource","reason"}]}

`done` is the `done` document of the LWS client's `list` or `read`
(`Wasm/Ops/LwsClient.lean`). Every decision is
`L4Factoidal.LWS.DatasetView` (`planListing`, `readOfDone`, `view`); the host
is `npm/factoidal/lws/dataset.mjs`.
-/
import Wasm.Ops.Support
import L4Factoidal.LWS.DatasetViewRead

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS.DatasetView

/-- `lwsViewPlan(listDoneJson)`: which members of a listing to list, read or
leave out. -/
def lwsViewPlan (text : String) : String :=
  match parseJson text with
  | .error _ => errJson "lwsViewPlan: the listing is not JSON"
  | .ok j => match planJson (planListing j) with
    | .object fs => okWith fs
    | _ => errJson "lwsViewPlan: internal"

/-- `lwsDatasetView(docsJson)`: the dataset view of the listings and reads,
as N-Quads, with the evidence. -/
def lwsDatasetView (text : String) : String :=
  match parseJson text with
  | .error _ => errJson "lwsDatasetView: the documents are not JSON"
  | .ok j => match viewOfDocsJson (docsOfJson j) with
    | .ok (.object fs) => okWith fs
    | .ok _ => errJson "lwsDatasetView: internal"
    | .error e => errJson s!"lwsDatasetView: {e}"

def lwsDatasetOpNames : List String := ["lwsViewPlan", "lwsDatasetView"]

-- A listing: one container, one Turtle resource, one PNG.
#guard (lwsViewPlan "{\"members\":[{\"id\":\"http://s/a/\",\"type\":\"Container\"},{\"id\":\"http://s/b.ttl\",\"type\":\"DataResource\",\"format\":\"text/turtle\"},{\"id\":\"http://s/c.png\",\"type\":\"DataResource\",\"format\":\"image/png\"}]}")
  = "{\"ok\":true,\"containers\":[\"http://s/a/\"],\"resources\":[\"http://s/b.ttl\"],\"skipped\":[{\"resource\":\"http://s/c.png\",\"reason\":\"no RDF reader for media type image/png\"}]}"
#guard (lwsViewPlan "not json").startsWith "{\"ok\":false"
-- One read: its graph is named by its IRI, its ETag is the evidence.
#guard (lwsDatasetView "{\"listings\":[{\"container\":\"http://s/\",\"done\":{\"members\":[{\"id\":\"http://s/b.ttl\"}]}}],\"reads\":[{\"resource\":\"http://s/b.ttl\",\"done\":{\"status\":200,\"headers\":[[\"content-type\",\"text/turtle\"],[\"etag\",\"\\\"7\\\"\"]],\"body\":\"<> <http://e/p> 1 .\"}}]}")
  = "{\"ok\":true,\"nquads\":\"<http://s/> <http://www.w3.org/ns/ldp#contains> <http://s/b.ttl> .\\n<http://s/b.ttl> <http://e/p> \\\"1\\\"^^<http://www.w3.org/2001/XMLSchema#integer> <http://s/b.ttl> .\\n\",\"graphs\":1,\"evidence\":[{\"resource\":\"http://s/b.ttl\",\"etag\":\"\\\"7\\\"\",\"lastModified\":\"\"}],\"skipped\":[]}"
-- A read with a media type that has no RDF reader is left out, with the reason.
#guard (lwsDatasetView "{\"reads\":[{\"resource\":\"http://s/c\",\"done\":{\"status\":200,\"headers\":[[\"content-type\",\"text/plain\"]],\"body\":\"x\"}}]}")
  = "{\"ok\":true,\"nquads\":\"\",\"graphs\":0,\"evidence\":[],\"skipped\":[{\"resource\":\"http://s/c\",\"reason\":\"no RDF reader for media type text/plain\"}]}"

end L4Wasm.Ops
