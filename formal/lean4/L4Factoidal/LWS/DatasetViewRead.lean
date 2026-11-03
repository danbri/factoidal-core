/-
L4Factoidal.LWS.DatasetViewRead — building the dataset view
(`LWS/DatasetView.lean`) from what an LWS client read
(https://github.com/danbri/factoidal/issues/1011, KR2 and KR3; version 2,
2026-11-03).

The host (`npm/factoidal/lws/dataset.mjs`) crawls a storage with the LWS
client (`LWS/Client/Machine.lean`, ops `lwsClientStart`/`lwsClientStep`) and
decides nothing. This module makes every decision of the crawl and of the
view, over the client's `done` documents:

* `planListing`: from the `done` document of a container `list`, which
  members are containers (to list), which are resources to read, which are
  left out (a media type with no RDF reader in the reader table,
  `RDF.formatOfMediaType`), and whose linksets to read (`metadata`: the
  listed container itself, then every member that is not a container; LWS
  1.0 Core, "Containers": a listing member's `type` and `format`).
* `entriesOfListing`: the listing members of the table-of-contents graph:
  kind, and for a data resource `format`, `size` and `modified`.
* `readOfDone`: from the `done` document of a `read` (LWS 1.0 Core, "Read
  Resource"), the entity tag (`ETag`, RFC 9110 §8.8.3), `Last-Modified`
  (RFC 9110 §8.8.2), the media type (`Content-Type`), and the graph: the
  reader of the media type (`Dataflow.readers`) applied to the
  representation, with the resource IRI as base IRI, in the blank-node scope
  of the read's position (`Dataset.scopeDocument`, RDF 1.1 Concepts §3.4).
  A dataset syntax (TriG, N-Quads) gives its default graph only.
* `linksetOfDone`: from the `done` document of a `readLinkset` (`linkset`,
  `url`, `etag`), the links of the `application/linkset+json` document
  (RFC 9264 §4.2): each link context object has an `anchor` (when it has
  none, the resource IRI) and members whose name is a relation type and whose
  value is an array of target objects with `href`. A relative `anchor` or
  `href` is resolved against the linkset IRI (RFC 3986 §5.2). The relation
  type becomes an IRI by `relIri`. Target attributes (`title`, `type`,
  `hreflang`) are not part of the view: that is the definition of the view.
  A link whose relation type has no IRI, or whose target object has no
  `href`, is left out with a reason.
* `storageOf?`: the storage description IRI, the target of the first link
  with relation `https://www.w3.org/ns/lws#storage` whose context is the
  storage root (the first container listed), in the first linkset read of
  the storage root. Without it there is no view: the storage description IRI
  is the name of the table-of-contents graph.
* `snapshotOfDocs`: the snapshot of the listings, reads and linkset reads;
  `viewOfDocsJson` its view, the evidence and the items left out.

Limits of this version (issue 1011): a full crawl, no search index, no
caching; one HEAD and one GET per resource for its linkset; the snapshot is a
sequence of GETs, not one read of the storage (`Dataflow/LwsSource.lean`,
the assumption `lwsReadsAtSnapshot`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.LWS.DatasetView
import L4Factoidal.LWS.Model
import L4Factoidal.LWS.Client.Wire
import L4Factoidal.Dataflow.Reader
import L4Factoidal.RDF.MediaType
import L4Factoidal.RDF.CertifiedDataset
import L4Factoidal.Syntax.IriResolve
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
  /-- Resources whose linkset to read: the listed container, then every
  member that is not a container (containers get theirs when they are
  listed). -/
  metadata : List String := []
  /-- Members left out, with the reason. -/
  skipped : List (String × String) := []
  deriving Repr, Inhabited

/-- A listing member's kind is a container (LWS 1.0 Core, "Containers"; the
JSON `type` of a member, `Container` or `StorageRoot`). -/
def memberIsContainer (m : Json) : Bool :=
  match m.getString? "type" with
  | some "Container" | some "StorageRoot" => true
  | _ => false

/-- Plan one member: list it, or read its linkset and read it (an RDF media
type, or no `format` given: the `Content-Type` of the read decides), or read
its linkset and leave the member out of the reads. -/
def planMember (p : ListingPlan) (m : Json) : ListingPlan :=
  match m.getString? "id" with
  | none => p
  | some id =>
    if memberIsContainer m then { p with containers := p.containers ++ [id] } else
    let p := { p with metadata := p.metadata ++ [id] }
    match m.getString? "format" with
    | none => { p with resources := p.resources ++ [id] }
    | some fmt =>
      if (formatOfMediaType fmt).isSome then { p with resources := p.resources ++ [id] }
      else { p with skipped := p.skipped ++ [(id, s!"no RDF reader for media type {fmt}")] }

/-- **The plan of a `list` `done` document** (`members`, each with `id`,
`type` and, for a data resource, `format`). `container` is the listed
container; when it is not given, the `id` of the document, when it has one. -/
def planListing (listDone : Json) (container : Option String := none) : ListingPlan :=
  let start : ListingPlan :=
    match container.orElse (fun _ => listDone.getString? "id") with
    | some c => { metadata := [c] }
    | none => {}
  ((listDone.getArray? "members").getD []).foldl planMember start

/-- The containment pairs of a listing: the container and each member id
that is an IRI. -/
def pairsOfListing (container : String) (listDone : Json) : List (WfIri × WfIri) :=
  match mkIri? container with
  | none => []
  | some c => ((listDone.getArray? "members").getD []).filterMap (fun m =>
      (m.getString? "id").bind mkIri? |>.map (fun i => (c, i)))

/-- The `size` of a listing member, as the lexical form of an `xsd:long`: a
JSON number of decimal digits only (the listing writes the byte count,
`LWS/Binding.lean` `itemJson`); any other value gives no `size` triple. -/
def sizeOf? (m : Json) : Option String :=
  match m.field? "size" with
  | some (.number n) => if !n.isEmpty && n.all Char.isDigit then some n else none
  | _ => none

/-- One listing member of the table-of-contents graph. -/
def entryOfMember (m : Json) : Option Entry := do
  let iri ← (m.getString? "id").bind mkIri?
  if memberIsContainer m then pure { resource := iri, kind := .container }
  else pure { resource := iri, kind := .dataResource, format := m.getString? "format"
              size := sizeOf? m, modified := m.getString? "modified" }

/-- The listing members of a `list` `done` document. -/
def entriesOfListing (listDone : Json) : List Entry :=
  ((listDone.getArray? "members").getD []).filterMap entryOfMember

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

/-! ## One linkset read -/

/-- The links and the reasons for the links left out, so far. -/
abbrev LinkAcc := List Link × List String

/-- The links of one target array of a relation type. -/
def linksOfTargets (base : String) (ctx rel : WfIri) (name : String) (acc : LinkAcc)
    (t : Json) : LinkAcc :=
  match t.getString? "href" with
  | none => (acc.1, acc.2 ++ [s!"relation {name}: a target object with no href"])
  | some h =>
    match iriOf? (Syntax.resolveIri base h) with
    | none => (acc.1, acc.2 ++ [s!"relation {name}: target {h} is not an IRI"])
    | some tgt => (acc.1 ++ [⟨ctx, rel, tgt⟩], acc.2)

/-- The links of one member of a link context object (RFC 9264 §4.2.3). -/
def linksOfMember (base : String) (ctx : WfIri) (acc : LinkAcc) (kv : String × Json) :
    LinkAcc :=
  let (name, v) := kv
  if name == "anchor" then acc else
  match relIri name with
  | none => (acc.1, acc.2 ++ [s!"relation {name}: neither a registered relation type name (RFC 8288 §3.3) nor an absolute IRI"])
  | some rel =>
    match v with
    | .array ts => ts.foldl (linksOfTargets base ctx rel name) acc
    | _ => (acc.1, acc.2 ++ [s!"relation {name}: the value is not an array of target objects (RFC 9264 §4.2.3)"])

/-- The links of one link context object (RFC 9264 §4.2.2). -/
def linksOfContext (base resource : String) (acc : LinkAcc) (c : Json) : LinkAcc :=
  match c with
  | .object fs =>
    let anchor := (c.getString? "anchor").getD resource
    match iriOf? (Syntax.resolveIri base anchor) with
    | none => (acc.1, acc.2 ++ [s!"link context {anchor} is not an IRI"])
    | some ctx => fs.foldl (linksOfMember base ctx) acc
  | _ => (acc.1, acc.2 ++ ["a link context that is not a JSON object"])

/-- **One linkset read from a `readLinkset` `done` document** (`linkset`,
`url`, `etag`), with the reasons for the links left out. -/
def linksetOfDone (resource : String) (done : Json) : Except String (LinksetRead × List String) := do
  let some res := mkIri? resource | throw s!"not an IRI: {resource}"
  let some url := done.getString? "url" | throw "the linkset read has no linkset IRI (url)"
  let some ls := mkIri? url | throw s!"the linkset IRI is not an IRI: {url}"
  let some ctxs := ((done.field? "linkset").getD .null).getArray? "linkset"
    | throw "the linkset document has no linkset array (RFC 9264 §4.2)"
  let (links, dropped) := ctxs.foldl (linksOfContext url resource) ([], [])
  pure ({ resource := res, linkset := ls, etag := (done.getString? "etag").getD "", links }, dropped)

/-! ## The snapshot and the view -/

/-- The input documents: each listing `(container, done)`, each read
`(resource, done)` and each linkset read `(resource, done)`. -/
structure Docs where
  listings : List (String × Json) := []
  reads : List (String × Json) := []
  linksets : List (String × Json) := []

/-- **The storage description IRI**: the target of the first link with
relation `lws#storage` whose context is the storage root (the first
container listed), in the first linkset read of the storage root. -/
def storageOf? (listings : List (String × Json)) (ls : List LinksetRead) : Option WfIri := do
  let (root, _) ← listings.head?
  let rootIri ← mkIri? root
  let l ← ls.find? (fun l => l.resource == rootIri)
  let k ← l.links.find? (fun k => k.rel == lwsStorageIri && k.context == rootIri)
  pure k.target

/-- The error when no linkset read gives the storage description IRI. -/
def storageMissing : String :=
  "the view needs the storage description IRI as the name of its table-of-contents graph: " ++
  "no linkset read of the storage root (the first container listed) has a link with relation " ++
  "https://www.w3.org/ns/lws#storage"

/-- Each read, parsed. -/
def readOuts (d : Docs) : List (String × Except String Read) :=
  d.reads.zipIdx.map (fun ((res, done), k) => (res, readOfDone k res done))

/-- Each linkset read, parsed. -/
def linksetOuts (d : Docs) : List (String × Except String (LinksetRead × List String)) :=
  d.linksets.map (fun (res, done) => (res, linksetOfDone res done))

/-- The linkset reads that parsed. -/
def linksetReadsOf (outs : List (String × Except String (LinksetRead × List String))) :
    List LinksetRead :=
  outs.filterMap (fun (_, o) => match o with | .ok (l, _) => some l | .error _ => none)

/-- The snapshot of the documents with the storage description IRI `st`, and
the items left out with the reason. -/
def snapshotWith (d : Docs) (louts : List (String × Except String (LinksetRead × List String)))
    (st : WfIri) : Snapshot × List (String × String) :=
  let outs := readOuts d
  ({ storage := st
     members := d.listings.flatMap (fun (c, l) => pairsOfListing c l)
     entries := d.listings.flatMap (fun (_, l) => entriesOfListing l)
     reads := outs.filterMap (fun (_, o) => match o with | .ok r => some r | .error _ => none)
     linksets := linksetReadsOf louts },
   outs.filterMap (fun (res, o) => match o with | .ok _ => none | .error e => some (res, e)) ++
   louts.flatMap (fun (res, o) => match o with
     | .ok (_, dropped) => dropped.map (fun why => (res, s!"linkset: {why}"))
     | .error e => [(res, s!"linkset: {e}")]))

/-- **The snapshot of the documents**, and the items left out with the
reason; an error when no linkset read gives the storage description IRI. -/
def snapshotOfDocs (d : Docs) : Except String (Snapshot × List (String × String)) :=
  match storageOf? d.listings (linksetReadsOf (linksetOuts d)) with
  | none => .error storageMissing
  | some st => .ok (snapshotWith d (linksetOuts d) st)

/-- The reason for an item whose IRI is already a graph name. -/
def clashReason : String :=
  "its IRI is already the name of another graph of the view (the table of contents, a " ++
  "document or a linkset): the first one is kept"

/-- The document and linkset reads left out of the view because their IRI is
already a graph name (`Snapshot.names`: the first wins). Two loops
(`List.foldl`). -/
def nameClashes (s : Snapshot) : List (String × String) :=
  let afterReads := s.reads.foldl (fun (acc : List WfIri × List (String × String)) r =>
      if acc.1.contains r.resource then (acc.1, acc.2 ++ [(r.resource.val, clashReason)])
      else (acc.1 ++ [r.resource], acc.2)) ([s.storage], [])
  (s.linksets.foldl (fun (acc : List WfIri × List (String × String)) l =>
      if acc.1.contains l.linkset then
        (acc.1, acc.2 ++ [(l.resource.val, s!"linkset {l.linkset.val}: {clashReason}")])
      else (acc.1 ++ [l.linkset], acc.2)) afterReads).2

/-- The evidence of a snapshot: each document read with its entity tag and
`Last-Modified`. -/
def evidenceOf (s : Snapshot) : List (String × String × String) :=
  s.reads.map (fun r => (r.resource.val, r.etag, r.lastModified))

/-- The evidence of the linkset reads: resource, linkset IRI, entity tag. -/
def linksetEvidenceOf (s : Snapshot) : List (String × String × String) :=
  s.linksets.map (fun l => (l.resource.val, l.linkset.val, l.etag))

/-- `{listings: [{container, done}], reads: [{resource, done}], linksets:
[{resource, done}]}`. -/
def docsOfJson (j : Json) : Docs :=
  let pairs (k a b : String) : List (String × Json) :=
    ((j.getArray? k).getD []).filterMap (fun x =>
      (x.getString? a).map (fun s => (s, (x.field? b).getD .null)))
  { listings := pairs "listings" "container" "done", reads := pairs "reads" "resource" "done"
    linksets := pairs "linksets" "resource" "done" }

/-- The view of the documents as N-Quads (of the certified view, so each
graph is a set), the number of named graphs, the name of the
table-of-contents graph, the evidence and the items left out, as JSON:
`{nquads, graphs, toc, evidence: [{resource, etag, lastModified} |
{resource, linkset, etag}], skipped: [{resource, reason}]}`. -/
def viewOfDocsJson (d : Docs) : Except String Json := do
  let (s, skipped) ← snapshotOfDocs d
  let nq ← L4Factoidal.Syntax.Dataset.toNQuads (view s).certify.val
  pure (.object
    [ ("nquads", .string nq)
    , ("graphs", .number (toString s.names.length))
    , ("toc", .string s.storage.val)
    , ("evidence", .array ((evidenceOf s).map (fun (r, e, lm) =>
          .object [("resource", .string r), ("etag", .string e), ("lastModified", .string lm)]) ++
        (linksetEvidenceOf s).map (fun (r, l, e) =>
          .object [("resource", .string r), ("linkset", .string l), ("etag", .string e)])))
    , ("skipped", .array ((skipped ++ nameClashes s).map (fun (r, why) =>
        .object [("resource", .string r), ("reason", .string why)]))) ])

/-- A plan as JSON: `{containers, resources, metadata, skipped: [{resource,
reason}]}`. -/
def planJson (p : ListingPlan) : Json :=
  .object
    [ ("containers", .array (p.containers.map Json.string))
    , ("resources", .array (p.resources.map Json.string))
    , ("metadata", .array (p.metadata.map Json.string))
    , ("skipped", .array (p.skipped.map (fun (r, why) =>
        .object [("resource", .string r), ("reason", .string why)]))) ]

/-! ## What the snapshot is made of -/

private theorem snapshotOfDocs_ok {d : Docs} {s : Snapshot} {sk : List (String × String)}
    (h : snapshotOfDocs d = .ok (s, sk)) :
    ∃ st, storageOf? d.listings (linksetReadsOf (linksetOuts d)) = some st ∧
      snapshotWith d (linksetOuts d) st = (s, sk) := by
  unfold snapshotOfDocs at h
  cases hst : storageOf? d.listings (linksetReadsOf (linksetOuts d)) with
  | none => rw [hst] at h; cases h
  | some st =>
    rw [hst] at h
    cases h
    exact ⟨st, rfl, rfl⟩

/-- The snapshot of the documents is built from the reads that parsed: each
of its reads is the read of a document. -/
theorem snapshotOfDocs_reads (d : Docs) (s : Snapshot) (sk : List (String × String))
    (h : snapshotOfDocs d = .ok (s, sk)) (r : Read) (hr : r ∈ s.reads) :
    ∃ res done k, readOfDone k res done = .ok r := by
  obtain ⟨st, _, hw⟩ := snapshotOfDocs_ok h
  have hs : s = (snapshotWith d (linksetOuts d) st).1 := by rw [hw]
  subst hs
  simp only [snapshotWith, readOuts, List.mem_filterMap, List.mem_map] at hr
  obtain ⟨⟨res, o⟩, ⟨⟨⟨res', done⟩, k⟩, _, he⟩, hr⟩ := hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨res', done, k, ?_⟩
  cases ho : readOfDone k res' done with
  | ok v => rw [ho] at hr; cases hr; rfl
  | error e => rw [ho] at hr; cases hr

/-- Each linkset read of the snapshot is the linkset read of a document. -/
theorem snapshotOfDocs_linksets (d : Docs) (s : Snapshot) (sk : List (String × String))
    (h : snapshotOfDocs d = .ok (s, sk)) (l : LinksetRead) (hl : l ∈ s.linksets) :
    ∃ res done dropped, linksetOfDone res done = .ok (l, dropped) := by
  obtain ⟨st, _, hw⟩ := snapshotOfDocs_ok h
  have hs : s = (snapshotWith d (linksetOuts d) st).1 := by rw [hw]
  subst hs
  simp only [snapshotWith, linksetReadsOf, linksetOuts, List.mem_filterMap, List.mem_map] at hl
  obtain ⟨⟨res, o⟩, ⟨⟨res', done⟩, _, he⟩, hl⟩ := hl
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases ho : linksetOfDone res' done with
  | ok v =>
    rw [ho] at hl
    obtain ⟨l', dropped⟩ := v
    cases hl
    exact ⟨res', done, dropped, ho⟩
  | error e => rw [ho] at hl; cases hl

/-- The name of the table-of-contents graph is the target of the
`lws#storage` link of the storage root in the snapshot's linkset reads. -/
theorem snapshotOfDocs_storage (d : Docs) (s : Snapshot) (sk : List (String × String))
    (h : snapshotOfDocs d = .ok (s, sk)) :
    storageOf? d.listings s.linksets = some s.storage := by
  obtain ⟨st, hst, hw⟩ := snapshotOfDocs_ok h
  have hs : s = (snapshotWith d (linksetOuts d) st).1 := by rw [hw]
  subst hs
  exact hst

/-- Without the storage description IRI there is no view. -/
theorem snapshotOfDocs_storage_missing (d : Docs)
    (h : storageOf? d.listings (linksetReadsOf (linksetOuts d)) = none) :
    snapshotOfDocs d = .error storageMissing := by
  unfold snapshotOfDocs
  rw [h]

#print axioms snapshotOfDocs_reads
#print axioms snapshotOfDocs_linksets
#print axioms snapshotOfDocs_storage
#print axioms snapshotOfDocs_storage_missing

end L4Factoidal.LWS.DatasetView
