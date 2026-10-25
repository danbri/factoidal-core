/-
L4Factoidal.LWS.DatasetViewRead — building the dataset view
(`LWS/DatasetView.lean`) from what an LWS client read
(https://github.com/danbri/factoidal/issues/1011, KR2 and KR3).

The host (`npm/factoidal/lws/dataset.mjs`) crawls a storage with the LWS
client (`LWS/Client/Machine.lean`, ops `lwsClientStart`/`lwsClientStep`) and
decides nothing. This module makes every decision of the crawl and of the
view, over the client's `done` documents:

* `planListing`: from the `done` document of a container `list`, which
  members are containers (to list), which are resources to read, and which
  are left out (a media type with no RDF reader in the reader table,
  `RDF.formatOfMediaType`; LWS 1.0 Core, "Containers": a listing member's
  `type` and `format`).
* `readOfDone`: from the `done` document of a `read` (LWS 1.0 Core, "Read
  Resource"), the entity tag (`ETag`, RFC 9110 §8.8.3), `Last-Modified`
  (RFC 9110 §8.8.2), the media type (`Content-Type`), and the graph: the
  reader of the media type (`Dataflow.readers`) applied to the
  representation, with the resource IRI as base IRI, in the blank-node scope
  of the read's position (`Dataset.scopeDocument`, RDF 1.1 Concepts §3.4).
  A dataset syntax (TriG, N-Quads) gives its default graph only.
* `snapshotOfDocs`: the snapshot of the listings and reads; `viewOfDocs` its
  view, the entity tags (the evidence) and the resources left out.

Limits of this first version (issue 1011): metadata resources are not
crawled (a listing does not enumerate them; the definition admits them); a
full crawl, no search index, no caching; the snapshot is a sequence of GETs,
not one read of the storage (`Dataflow/LwsSource.lean`, the assumption
`lwsReadsAtSnapshot`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.LWS.DatasetView
import L4Factoidal.LWS.Model
import L4Factoidal.LWS.Client.Wire
import L4Factoidal.Dataflow.Reader
import L4Factoidal.RDF.MediaType
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.LWS.DatasetView

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.LWS.Client (respOfJson Resp)

/-! ## The crawl plan of one listing -/

/-- What to do with the members of one container listing. -/
structure ListingPlan where
  /-- Members that are containers: list them. -/
  containers : List String := []
  /-- Members to read. -/
  resources : List String := []
  /-- Members left out, with the reason. -/
  skipped : List (String × String) := []
  deriving Repr, Inhabited

/-- A listing member's kind is a container (LWS 1.0 Core, "Containers"; the
JSON `type` of a member, `Container` or `StorageRoot`). -/
def memberIsContainer (m : Json) : Bool :=
  match m.getString? "type" with
  | some "Container" | some "StorageRoot" => true
  | _ => false

/-- Plan one member: list it, read it (an RDF media type, or no `format`
given: the `Content-Type` of the read decides), or leave it out. -/
def planMember (p : ListingPlan) (m : Json) : ListingPlan :=
  match m.getString? "id" with
  | none => p
  | some id =>
    if memberIsContainer m then { p with containers := p.containers ++ [id] } else
    match m.getString? "format" with
    | none => { p with resources := p.resources ++ [id] }
    | some fmt =>
      if (formatOfMediaType fmt).isSome then { p with resources := p.resources ++ [id] }
      else { p with skipped := p.skipped ++ [(id, s!"no RDF reader for media type {fmt}")] }

/-- **The plan of a `list` `done` document** (`members`, each with `id`,
`type` and, for a data resource, `format`). -/
def planListing (listDone : Json) : ListingPlan :=
  ((listDone.getArray? "members").getD []).foldl planMember {}

/-- The containment pairs of a listing: the container and each member id
that is an IRI. -/
def pairsOfListing (container : String) (listDone : Json) : List (WfIri × WfIri) :=
  match mkIri? container with
  | none => []
  | some c => ((listDone.getArray? "members").getD []).filterMap (fun m =>
      (m.getString? "id").bind mkIri? |>.map (fun i => (c, i)))

/-! ## One read -/

/-- **One read from a `read` `done` document** (`status`, `headers`, `body`
or `bodyBase64`), in blank-node scope `k`. -/
def readOfDone (k : Nat) (resource : String) (done : Json) : Except String Read := do
  let r : Resp := respOfJson done
  let some iri := mkIri? resource | throw s!"not an IRI: {resource}"
  unless r.ok do throw s!"status {r.status}"
  let ct := (r.header? "content-type").getD ""
  let some fmt := formatOfMediaType ct | throw s!"no RDF reader for media type {ct}"
  let some text := String.fromUTF8? r.body | throw "the representation is not UTF-8"
  match (Dataflow.readers {} fmt).dataset { text, base := some resource } with
  | .error e => throw s!"parse: {repr e}"
  | .ok ds =>
    pure { resource := iri, etag := (r.header? "etag").getD ""
           lastModified := (r.header? "last-modified").getD ""
           graph := (ds.scopeDocument k).default }

/-! ## The snapshot and the view -/

/-- The input documents: each listing `(container, done)` and each read
`(resource, done)`. -/
structure Docs where
  listings : List (String × Json) := []
  reads : List (String × Json) := []

/-- The snapshot of the documents, and the reads left out with the reason. -/
def snapshotOfDocs (d : Docs) : Snapshot × List (String × String) :=
  let outs := d.reads.zipIdx.map (fun ((res, done), k) => (res, readOfDone k res done))
  ({ members := d.listings.flatMap (fun (c, l) => pairsOfListing c l)
     reads := outs.filterMap (fun (_, o) => match o with | .ok r => some r | .error _ => none) },
   outs.filterMap (fun (res, o) => match o with | .ok _ => none | .error e => some (res, e)))

/-- The evidence of a snapshot: each read resource and its entity tag. -/
def evidenceOf (s : Snapshot) : List (String × String × String) :=
  s.reads.map (fun r => (r.resource.val, r.etag, r.lastModified))

/-- `{listings: [{container, done}], reads: [{resource, done}]}`. -/
def docsOfJson (j : Json) : Docs :=
  let pairs (k a b : String) : List (String × Json) :=
    ((j.getArray? k).getD []).filterMap (fun x =>
      (x.getString? a).map (fun s => (s, (x.field? b).getD .null)))
  { listings := pairs "listings" "container" "done", reads := pairs "reads" "resource" "done" }

/-- The view of the documents as N-Quads, the evidence and the left-out
reads, as JSON: `{nquads, graphs, evidence: [{resource, etag,
lastModified}], skipped: [{resource, reason}]}`. -/
def viewOfDocsJson (d : Docs) : Except String Json := do
  let (s, skipped) := snapshotOfDocs d
  let nq ← L4Factoidal.Syntax.Dataset.toNQuads (view s)
  pure (.object
    [ ("nquads", .string nq)
    , ("graphs", .number (toString s.resources.length))
    , ("evidence", .array ((evidenceOf s).map (fun (r, e, lm) =>
        .object [("resource", .string r), ("etag", .string e), ("lastModified", .string lm)])))
    , ("skipped", .array (skipped.map (fun (r, why) =>
        .object [("resource", .string r), ("reason", .string why)]))) ])

/-- A plan as JSON: `{containers, resources, skipped: [{resource, reason}]}`. -/
def planJson (p : ListingPlan) : Json :=
  .object
    [ ("containers", .array (p.containers.map Json.string))
    , ("resources", .array (p.resources.map Json.string))
    , ("skipped", .array (p.skipped.map (fun (r, why) =>
        .object [("resource", .string r), ("reason", .string why)]))) ]

/-- The snapshot of the documents is built from the reads that parsed: each
of its reads is the read of a document. -/
theorem snapshotOfDocs_reads (d : Docs) (r : Read) (h : r ∈ (snapshotOfDocs d).1.reads) :
    ∃ res done k, readOfDone k res done = .ok r := by
  simp only [snapshotOfDocs, List.mem_filterMap, List.mem_map] at h
  obtain ⟨⟨res, o⟩, ⟨⟨⟨res', done⟩, k⟩, _, he⟩, hr⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨res', done, k, ?_⟩
  cases ho : readOfDone k res' done with
  | ok v => rw [ho] at hr; cases hr; rfl
  | error e => rw [ho] at hr; cases hr

#print axioms snapshotOfDocs_reads

end L4Factoidal.LWS.DatasetView
