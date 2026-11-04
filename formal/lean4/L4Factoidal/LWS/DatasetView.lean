/-
L4Factoidal.LWS.DatasetView — the dataset view of a Linked Web Storage
snapshot (https://github.com/danbri/factoidal/issues/1011), version 2
(2026-11-03).

Source specifications:

* Linked Web Storage Protocol 1.0 Core,
  <https://w3c.github.io/lws-protocol/lws10-core/> (W3C Linked Web Storage
  Working Group editor's draft): "Terminology" (an LWS resource, a container,
  a data resource, a metadata resource, containment), "Containers" (a
  container enumerates its members; the listing gives each member's `type`,
  `format`, `size` and `modified`), "Read Resource" (a GET answers a
  representation with `ETag` and `Last-Modified`), and the links of every
  resource (`linkset`, `up`, `type`, `https://www.w3.org/ns/lws#storage`).
* RFC 9264 (Linkset), §4.2: the `application/linkset+json` document, an
  object with a `linkset` array of link context objects.
* RFC 8288 (Web Linking), §2.1.1 and Appendix A.2: relation types.

**LWS 1.0 does not define this view.** The draft defines resources and their
representations; it says nothing about an RDF dataset made from a storage.
The definition below is Factoidal's (owner, 2026-10-25 and 2026-11-03, issue
1011), and it is a question for the LWS Working Group
(`docs/designissues/2026-10-25-lws-dataset-view.md`).

## The definition

A snapshot is what a client read from one storage:

* `storage`: the storage description IRI (the target of the
  `lws#storage` link of the storage root);
* `members`: the containment pairs of the container listings read;
* `entries`: for each listing member, its kind (container or data resource)
  and, for a data resource, the listing's `format`, `size` and `modified`;
* `reads`: for each RDF resource read, the resource IRI, the entity tag and
  `Last-Modified` of the representation, and the RDF graph that
  representation denotes (RDF 1.1 Concepts §3);
* `linksets`: for each linkset read, the resource IRI, the linkset IRI, its
  entity tag, and its links as (context, relation IRI, target).

The view (`view`) is the RDF dataset (RDF 1.1 Concepts §4):

* the **default graph** is empty;
* the **table-of-contents graph** (`Snapshot.toc`) is the first named graph.
  Its name is the storage description IRI. It holds the RDF of the listings
  and the links from the documents to their metadata:
  `<container> lws:items <member>` for each containment pair;
  `<member> rdf:type lws:Container` or `lws:DataResource`; for a data
  resource with listing values `<member> dcterms:format "fmt"`,
  `<member> schema:size "n"^^xsd:long` and
  `<member> dcterms:modified "t"^^xsd:dateTime` (the predicates of the
  Turtle form of a listing, `LWS/Binding.lean` `containerTurtle`); and
  `<resource> <http://www.iana.org/assignments/relation/linkset> <linkset>`
  for each linkset read;
* one named graph per RDF document read, whose name is the resource IRI and
  whose triples are the graph its representation denotes;
* one named graph per linkset read, whose name is the linkset IRI and whose
  triples are `<context> <relIri rel> <target>`.

The names are distinct by construction (`Snapshot.names`): the table-of-
contents name first, then the document IRIs, then the linkset IRIs, in
order. An item whose IRI is already a name is left out: the first wins.

Non-RDF resources have no document graph: a reader that has no RDF reader for
a representation's media type leaves the resource out of `reads`. They are in
the table-of-contents graph (from the listing) and have a linkset graph when
their linkset was read.

Blank nodes: RDF 1.1 Concepts §3.4 scopes blank nodes to a document, so the
graphs of two reads share no blank node. The readers give each document its
own scope (`Dataset.scopeDocument`); this module takes the graphs as given.

## Properties (proved below)

* `view_names_nodup`: the graph names of the view are distinct.
* `view_names`, `view_mem_names`: the names are the storage description IRI,
  then the document IRIs and the linkset IRIs, each once (`mem_names`).
* `view_toc_first`, `view_lookup_toc`: the first named graph is named by the
  storage description IRI, and its graph is the table-of-contents graph.
* `view_replace`: replacing one document's representation
  (`Snapshot.replace`) leaves the default graph and the list of names
  unchanged, and changes the named graph of that IRI only, when that graph is
  the document's graph; the table-of-contents graph and the linkset graphs
  do not change. `view_replace_lookup` states it per name.
* `view_lookup`, `view_lookup_linkset`: the graph named by a document IRI is
  the graph of its first read; the graph named by a linkset IRI that is no
  other name is the graph of its first linkset read.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.LWS.DatasetView

open L4Factoidal.RDF

/-! ## Vocabulary -/

/-- `lws:items` (the LWS vocabulary, `https://www.w3.org/ns/lws#`): the
containment predicate of the table-of-contents graph. -/
def lwsItemsIri : WfIri := ⟨"https://www.w3.org/ns/lws#items", by decide⟩
/-- `lws:Container`. -/
def lwsContainerIri : WfIri := ⟨"https://www.w3.org/ns/lws#Container", by decide⟩
/-- `lws:DataResource`. -/
def lwsDataResourceIri : WfIri := ⟨"https://www.w3.org/ns/lws#DataResource", by decide⟩
/-- The relation type of the link from a resource to its storage description
(LWS 1.0 Core, "Discovery"). -/
def lwsStorageIri : WfIri := ⟨"https://www.w3.org/ns/lws#storage", by decide⟩
/-- `rdf:type`. -/
def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", by decide⟩
/-- `dcterms:format`. -/
def dctermsFormatIri : WfIri := ⟨"http://purl.org/dc/terms/format", by decide⟩
/-- `dcterms:modified`. -/
def dctermsModifiedIri : WfIri := ⟨"http://purl.org/dc/terms/modified", by decide⟩
/-- `schema:size`, in the namespace `http://schema.org/` that
`LWS/Binding.lean` `containerTurtle` uses (the reasons are there). -/
def schemaSizeIri : WfIri := ⟨"http://schema.org/size", by decide⟩
/-- `xsd:long`. -/
def xsdLongIri : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#long", by decide⟩
/-- `xsd:dateTime`. -/
def xsdDateTimeIri : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", by decide⟩
/-- The base IRI of registered relation types, RFC 8288 Appendix A.2. -/
def ianaRelationBase : String := "http://www.iana.org/assignments/relation/"
/-- The registered relation type `linkset` (RFC 9264 §6), as an IRI. -/
def ianaLinksetIri : WfIri := ⟨"http://www.iana.org/assignments/relation/linkset", by decide⟩

/-- An IRI, or nothing. -/
def iriOf? (s : String) : Option WfIri :=
  if h : isIri s = true then some ⟨s, h⟩ else none

/-- A registered relation type name (RFC 8288 §3.3: `reg-rel-type = LOALPHA
*( LOALPHA / DIGIT / "." / "-" )`). -/
def isRegRelName (name : String) : Bool :=
  match name.toList with
  | c :: cs => c.isLower && cs.all (fun d => d.isLower || d.isDigit || d == '.' || d == '-')
  | [] => false

/-- **The IRI of a relation type** of a linkset (RFC 9264 §4.2.3: the member
name of a link context object is a relation type).

* A relation type that is an absolute IRI (an extension relation type,
  RFC 8288 §2.1.2) is the IRI as it is.
* `items` is `https://www.w3.org/ns/lws#items` and `type` is `rdf:type`: the
  LWS vocabulary defines `items`, and the `application/lws+json` context maps
  `type` to `@type` (owner, 2026-11-03: relation IRIs are "LWS vocab where
  defined").
* Every other registered relation type name, lower-cased, is the name after
  `http://www.iana.org/assignments/relation/`, the base of RFC 8288 Appendix
  A.2. RFC 8288 §2.1.1 says registered relation type names are compared
  case-insensitively, so the name is lower-cased first. The same section says
  that converting a registered relation type to a URI in this way is "NOT
  RECOMMENDED" for comparison with extension relation types; the view is a
  serialisation of the links in RDF, and this function states the mapping it
  uses.
* A relation type that is neither (not a registered name, no colon) has no
  IRI: the link is left out. -/
def relIri (rel : String) : Option WfIri :=
  if rel.contains ':' then iriOf? rel
  else
    let name := rel.toLower
    if name == "items" then some lwsItemsIri
    else if name == "type" then some rdfTypeIri
    else if isRegRelName name then iriOf? (ianaRelationBase ++ name)
    else none

/-! ## The snapshot -/

/-- What a read resource is to the storage (LWS 1.0 Core, "Terminology"). The
view treats both the same; the role is kept for the evidence. -/
inductive Role where
  /-- A data resource. -/
  | data
  /-- A metadata resource (an auxiliary resource that describes another). -/
  | metadata
  deriving DecidableEq, Repr, Inhabited

/-- One GET of an RDF resource (LWS 1.0 Core, "Read Resource"): the resource
IRI, the entity tag and `Last-Modified` of the representation, and the RDF
graph the representation denotes. -/
structure Read where
  resource : WfIri
  etag : String
  lastModified : String := ""
  role : Role := .data
  graph : Graph
  deriving Repr

/-- The kind of a listing member (LWS 1.0 Core, "Containers": the `type` of
a member, `Container` or `DataResource`). -/
inductive Kind where
  | container
  | dataResource
  deriving DecidableEq, Repr, Inhabited

/-- One listing member: its IRI and kind, and for a data resource the
listing's `format`, `size` (the lexical form of an `xsd:long`) and `modified`
(the lexical form of an `xsd:dateTime`) when the listing gives them. -/
structure Entry where
  resource : WfIri
  kind : Kind
  format : Option String := none
  size : Option String := none
  modified : Option String := none
  deriving Repr

/-- One link of a linkset: the link context, the relation type as an IRI
(`relIri`), and the link target (RFC 8288 §2). Target attributes (`title`,
`type`, `hreflang`) are not part of the view. -/
structure Link where
  context : WfIri
  rel : WfIri
  target : WfIri
  deriving DecidableEq, Repr

/-- One GET of the linkset of a resource (RFC 9264 §4.2): the resource IRI,
the linkset IRI, its entity tag and its links. -/
structure LinksetRead where
  resource : WfIri
  linkset : WfIri
  etag : String := ""
  links : List Link
  deriving Repr

/-- What a client read from one storage. -/
structure Snapshot where
  /-- The storage description IRI: the name of the table-of-contents graph. -/
  storage : WfIri
  /-- The containment pairs `(container, member)` of the listings. -/
  members : List (WfIri × WfIri)
  /-- The listing members. -/
  entries : List Entry := []
  /-- The RDF documents read. -/
  reads : List Read
  /-- The linksets read. -/
  linksets : List LinksetRead := []
  deriving Repr

/-! ## Names, each once -/

/-- Add an IRI at the end unless it is already in the list. -/
def addNew (acc : List WfIri) (i : WfIri) : List WfIri :=
  if acc.contains i then acc else acc ++ [i]

/-- `acc` followed by the IRIs of `xs` that are not yet in it, each once, in
first order. A loop (`List.foldl`), so its depth does not grow with the
list. -/
def dedupFrom (acc xs : List WfIri) : List WfIri := xs.foldl addNew acc

/-- The IRIs of a list of reads, each once, in first-read order. -/
def resourcesOf (rs : List Read) : List WfIri := dedupFrom [] (rs.map (·.resource))

/-- The IRIs of the RDF documents of a snapshot, each once. -/
def Snapshot.resources (s : Snapshot) : List WfIri := resourcesOf s.reads

/-- **The graph names of the view**: the storage description IRI, then the
document IRIs, then the linkset IRIs, each once; the first wins. -/
def Snapshot.names (s : Snapshot) : List WfIri :=
  dedupFrom [s.storage] (s.reads.map (·.resource) ++ s.linksets.map (·.linkset))

/-! ## The graphs -/

/-- An `xsd:long` literal with the lexical form `lex`. -/
def longLiteral (lex : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := xsdLongIri, langTag := none, direction := none }, rfl⟩

/-- An `xsd:dateTime` literal with the lexical form `lex`. -/
def dateTimeLiteral (lex : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := xsdDateTimeIri, langTag := none, direction := none }, rfl⟩

/-- The triples of one listing member in the table-of-contents graph. -/
def entryTriples (e : Entry) : Graph :=
  match e.kind with
  | .container => [⟨.iri e.resource, rdfTypeIri, .iri lwsContainerIri⟩]
  | .dataResource =>
    [⟨.iri e.resource, rdfTypeIri, .iri lwsDataResourceIri⟩] ++
    (match e.format with
     | some f => [⟨.iri e.resource, dctermsFormatIri, .literal (Literal.string f)⟩]
     | none => []) ++
    (match e.size with
     | some n => [⟨.iri e.resource, schemaSizeIri, .literal (longLiteral n)⟩]
     | none => []) ++
    (match e.modified with
     | some t => [⟨.iri e.resource, dctermsModifiedIri, .literal (dateTimeLiteral t)⟩]
     | none => [])

/-- **The table-of-contents graph**: the containment (`lws:items`), the
listing members, and the link from each resource to its linkset. -/
def Snapshot.toc (s : Snapshot) : Graph :=
  s.members.map (fun cm => ⟨.iri cm.1, lwsItemsIri, .iri cm.2⟩) ++
  s.entries.flatMap entryTriples ++
  s.linksets.map (fun l => ⟨.iri l.resource, ianaLinksetIri, .iri l.linkset⟩)

/-- The graph of a linkset read: one triple per link. -/
def LinksetRead.graph (l : LinksetRead) : Graph :=
  l.links.map (fun k => ⟨.iri k.context, k.rel, .iri k.target⟩)

/-- The graph of the first read of the IRI `i`, or the empty graph. -/
def Snapshot.graphOf (s : Snapshot) (i : WfIri) : Graph :=
  match s.reads.find? (fun r => r.resource == i) with
  | some r => r.graph
  | none => []

/-- The graph of the first linkset read whose linkset IRI is `i`, or the
empty graph. -/
def Snapshot.linksetGraphOf (s : Snapshot) (i : WfIri) : Graph :=
  match s.linksets.find? (fun l => l.linkset == i) with
  | some l => l.graph
  | none => []

/-- The graph named `i` in the view: the table-of-contents graph for the
storage description IRI, else the graph of the first document read of `i`,
else the graph of the first linkset read of `i`. -/
def Snapshot.graphFor (s : Snapshot) (i : WfIri) : Graph :=
  if i = s.storage then s.toc
  else match s.reads.find? (fun r => r.resource == i) with
    | some r => r.graph
    | none => s.linksetGraphOf i

/-- **The dataset view of a snapshot.** The default graph is empty; the named
graphs are the table-of-contents graph, the documents and the linksets. -/
def view (s : Snapshot) : Dataset :=
  { default := []
    named := s.names.map (fun i => ⟨.iri i, s.graphFor i⟩) }

/-- One read with the representation `etag`, `g` when it is a read of `i`. -/
def replaceRead (i : WfIri) (etag : String) (g : Graph) (r : Read) : Read :=
  if r.resource = i then { r with etag, graph := g } else r

/-- The snapshot with the representation of `i` replaced: every read of `i`
gets the entity tag `etag` and the graph `g`; nothing else changes. -/
def Snapshot.replace (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) : Snapshot :=
  { s with reads := s.reads.map (replaceRead i etag g) }

/-! ## Names, each once: proofs -/

private theorem addNew_of_mem {acc : List WfIri} {x : WfIri} (h : x ∈ acc) :
    addNew acc x = acc := by
  unfold addNew
  rw [if_pos (by simpa using h)]

private theorem addNew_of_not_mem {acc : List WfIri} {x : WfIri} (h : x ∉ acc) :
    addNew acc x = acc ++ [x] := by
  unfold addNew
  rw [if_neg (by simpa using h)]

private theorem dedup_spec (xs : List WfIri) :
    ∀ acc : List WfIri, acc.Nodup →
      (xs.foldl addNew acc).Nodup ∧ ∀ i, i ∈ xs.foldl addNew acc ↔ i ∈ acc ∨ i ∈ xs := by
  induction xs with
  | nil => intro acc h; simp [h]
  | cons x rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    by_cases hm : x ∈ acc
    · rw [addNew_of_mem hm]
      obtain ⟨h1, h2⟩ := ih acc hacc
      refine ⟨h1, fun i => ?_⟩
      rw [h2 i]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl hm
          · exact Or.inr h'
    · rw [addNew_of_not_mem hm]
      have hacc' : (acc ++ [x]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hacc, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb e
        rw [List.mem_singleton] at hb
        subst hb; subst e
        exact hm ha
      obtain ⟨h1, h2⟩ := ih _ hacc'
      refine ⟨h1, fun i => ?_⟩
      rw [h2 i, List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr h'

private theorem dedup_prefix (xs : List WfIri) :
    ∀ acc : List WfIri, ∃ t, xs.foldl addNew acc = acc ++ t := by
  induction xs with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons x rest ih =>
    intro acc
    simp only [List.foldl_cons]
    obtain ⟨t, ht⟩ := ih (addNew acc x)
    rw [ht]
    by_cases hm : x ∈ acc
    · rw [addNew_of_mem hm]; exact ⟨t, rfl⟩
    · rw [addNew_of_not_mem hm]; exact ⟨[x] ++ t, by rw [List.append_assoc]⟩

/-- Each document IRI is listed once. -/
theorem resources_nodup (s : Snapshot) : s.resources.Nodup :=
  (dedup_spec _ [] List.nodup_nil).1

/-- The listed IRIs are exactly the IRIs of the reads. -/
theorem mem_resources (s : Snapshot) (i : WfIri) :
    i ∈ s.resources ↔ ∃ r ∈ s.reads, r.resource = i := by
  rw [Snapshot.resources, resourcesOf, dedupFrom, (dedup_spec _ [] List.nodup_nil).2 i]
  simp

/-- A map that keeps every IRI keeps the list of IRIs. -/
theorem resourcesOf_map (f : Read → Read) (hf : ∀ r, (f r).resource = r.resource)
    (rs : List Read) : resourcesOf (rs.map f) = resourcesOf rs := by
  unfold resourcesOf
  rw [List.map_map]
  congr 2
  funext r
  exact hf r

/-- The graph names are distinct. -/
theorem names_nodup (s : Snapshot) : s.names.Nodup :=
  (dedup_spec _ [s.storage] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)).1

/-- The graph names are the storage description IRI, the document IRIs and the
linkset IRIs. -/
theorem mem_names (s : Snapshot) (i : WfIri) :
    i ∈ s.names ↔ i = s.storage ∨ (∃ r ∈ s.reads, r.resource = i) ∨
      (∃ l ∈ s.linksets, l.linkset = i) := by
  rw [Snapshot.names, dedupFrom,
    (dedup_spec _ [s.storage] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)).2 i]
  simp only [List.mem_singleton, List.mem_append, List.mem_map]

/-- The first graph name is the storage description IRI. -/
theorem names_head (s : Snapshot) : ∃ t, s.names = s.storage :: t := by
  obtain ⟨t, ht⟩ := dedup_prefix (s.reads.map (·.resource) ++ s.linksets.map (·.linkset)) [s.storage]
  exact ⟨t, ht⟩

/-! ## The graph names of the view -/

/-- The graph names of the view are the names of the snapshot, in order. -/
theorem view_names (s : Snapshot) : (view s).names = s.names.map Subject.iri := by
  show ((s.names.map (fun i => (⟨.iri i, s.graphFor i⟩ : NamedGraph))).map (·.name)) = _
  rw [List.map_map]
  rfl

/-- **The graph names of the view are distinct.** -/
theorem view_names_nodup (s : Snapshot) : (view s).names.Nodup := by
  rw [view_names]
  exact List.Pairwise.map Subject.iri (fun _ _ h e => h (Subject.iri.inj e)) (names_nodup s)

/-- A name of the view is the storage description IRI, the IRI of a document
read or the IRI of a linkset read. -/
theorem view_mem_names (s : Snapshot) (n : Subject) :
    n ∈ (view s).names ↔ n = .iri s.storage ∨ (∃ r ∈ s.reads, n = .iri r.resource) ∨
      (∃ l ∈ s.linksets, n = .iri l.linkset) := by
  rw [view_names, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (mem_names s i).mp hi with rfl | ⟨r, hr, e⟩ | ⟨l, hl, e⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨r, hr, e ▸ rfl⟩)
    · exact Or.inr (Or.inr ⟨l, hl, e ▸ rfl⟩)
  · rintro (rfl | ⟨r, hr, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨s.storage, (mem_names s _).mpr (Or.inl rfl), rfl⟩
    · exact ⟨r.resource, (mem_names s _).mpr (Or.inr (Or.inl ⟨r, hr, rfl⟩)), rfl⟩
    · exact ⟨l.linkset, (mem_names s _).mpr (Or.inr (Or.inr ⟨l, hl, rfl⟩)), rfl⟩

/-- The default graph of the view is empty. -/
theorem view_default (s : Snapshot) : (view s).default = [] := rfl

/-! ## The table-of-contents graph -/

theorem graphFor_storage (s : Snapshot) : s.graphFor s.storage = s.toc := by
  unfold Snapshot.graphFor
  rw [if_pos rfl]

theorem graphFor_of_ne (s : Snapshot) (i : WfIri) (h : i ≠ s.storage) :
    s.graphFor i = match s.reads.find? (fun r => r.resource == i) with
      | some r => r.graph
      | none => s.linksetGraphOf i := by
  unfold Snapshot.graphFor
  rw [if_neg h]

/-- **The first named graph of the view is the table-of-contents graph**, and
its name is the storage description IRI. -/
theorem view_toc_first (s : Snapshot) :
    (view s).named.head? = some ⟨.iri s.storage, s.toc⟩ := by
  obtain ⟨t, ht⟩ := names_head s
  show (s.names.map (fun i => (⟨.iri i, s.graphFor i⟩ : NamedGraph))).head? = _
  rw [ht, List.map_cons, List.head?_cons, graphFor_storage]

/-- The graph named by a name of the view is `graphFor` of it. -/
theorem view_lookup_name (s : Snapshot) (j : WfIri) (hj : j ∈ s.names) :
    (view s).lookupNamed (.iri j) = some (s.graphFor j) := by
  unfold Dataset.lookupNamed
  show (match (s.names.map (fun k => (⟨.iri k, s.graphFor k⟩ : NamedGraph))).find?
      (fun ng => ng.name == Subject.iri j) with
    | some ng => some ng.graph | none => none) = _
  rw [List.find?_map]
  cases hf : s.names.find? ((fun ng : NamedGraph => ng.name == Subject.iri j) ∘
      (fun k => (⟨.iri k, s.graphFor k⟩ : NamedGraph))) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf j hj
    simp at this
  | some k =>
    have hk := List.find?_some hf
    simp only [Function.comp, beq_iff_eq, Subject.iri.injEq] at hk
    subst hk
    rfl

/-- The graph named by the storage description IRI is the table-of-contents
graph. -/
theorem view_lookup_toc (s : Snapshot) :
    (view s).lookupNamed (.iri s.storage) = some s.toc := by
  rw [view_lookup_name s s.storage ((mem_names s _).mpr (Or.inl rfl)), graphFor_storage]

/-- The graph named by a document IRI (that is not the storage description
IRI) is the graph of its first read. -/
theorem view_lookup (s : Snapshot) (i : WfIri) (hi : i ∈ s.resources) (hs : i ≠ s.storage) :
    (view s).lookupNamed (.iri i) = some (s.graphOf i) := by
  obtain ⟨r, hr, e⟩ := (mem_resources s i).mp hi
  rw [view_lookup_name s i ((mem_names s _).mpr (Or.inr (Or.inl ⟨r, hr, e⟩))),
    graphFor_of_ne s i hs]
  unfold Snapshot.graphOf
  cases hf : s.reads.find? (fun r => r.resource == i) with
  | none => exact absurd (List.find?_eq_none.mp hf r hr) (by simp [e])
  | some r' => rfl

/-- The graph named by a linkset IRI that is no other name is the graph of
its first linkset read. -/
theorem view_lookup_linkset (s : Snapshot) (l : LinksetRead) (hl : l ∈ s.linksets)
    (hs : l.linkset ≠ s.storage) (hr : l.linkset ∉ s.resources) :
    (view s).lookupNamed (.iri l.linkset) = some (s.linksetGraphOf l.linkset) := by
  rw [view_lookup_name s l.linkset ((mem_names s _).mpr (Or.inr (Or.inr ⟨l, hl, rfl⟩))),
    graphFor_of_ne s l.linkset hs]
  cases hf : s.reads.find? (fun r => r.resource == l.linkset) with
  | none => rfl
  | some r =>
    exfalso
    have hrl : r.resource = l.linkset := Subtype.ext (by simpa using List.find?_some hf)
    exact hr ((mem_resources s _).mpr ⟨r, List.mem_of_find?_eq_some hf, hrl⟩)

/-! ## A document change changes one graph -/

theorem replaceRead_resource (i : WfIri) (etag : String) (g : Graph) (r : Read) :
    (replaceRead i etag g r).resource = r.resource := by
  unfold replaceRead
  split <;> rfl

theorem replace_resources (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (s.replace i etag g).resources = s.resources :=
  resourcesOf_map (replaceRead i etag g) (replaceRead_resource i etag g) s.reads

theorem replace_names (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (s.replace i etag g).names = s.names := by
  have h : (s.reads.map (replaceRead i etag g)).map (·.resource) = s.reads.map (·.resource) := by
    rw [List.map_map]
    congr 1
    funext r
    exact replaceRead_resource i etag g r
  show dedupFrom [s.storage] ((s.reads.map (replaceRead i etag g)).map (·.resource) ++
    s.linksets.map (·.linkset)) = _
  rw [h]
  rfl

/-- The table-of-contents graph does not depend on the documents read. -/
theorem replace_toc (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (s.replace i etag g).toc = s.toc := rfl

private theorem replace_find (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) (j : WfIri) :
    (s.replace i etag g).reads.find? (fun r => r.resource == j) =
      (s.reads.find? (fun r => r.resource == j)).map (replaceRead i etag g) := by
  show (s.reads.map (replaceRead i etag g)).find? _ = _
  rw [List.find?_map]
  have hp : ((fun r : Read => r.resource == j) ∘ replaceRead i etag g) = (fun r => r.resource == j) := by
    funext r
    simp [Function.comp, replaceRead_resource]
  rw [hp]

/-- The graph named `j` after a change of `i`: `g` when `j` is `i` and `i` is
a document name; otherwise the graph before. -/
theorem replace_graphFor (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) (j : WfIri) :
    (s.replace i etag g).graphFor j =
      if j = i ∧ i ∈ s.resources ∧ i ≠ s.storage then g else s.graphFor j := by
  by_cases hjs : j = s.storage
  · subst hjs
    rw [if_neg (fun h => h.2.2 h.1.symm)]
    exact (graphFor_storage (s.replace i etag g)).trans (graphFor_storage s).symm
  · rw [graphFor_of_ne (s.replace i etag g) j hjs, graphFor_of_ne s j hjs, replace_find]
    cases hf : s.reads.find? (fun r => r.resource == j) with
    | none =>
      have hnj : j ∉ s.resources := by
        intro hj
        obtain ⟨r, hr, e⟩ := (mem_resources s j).mp hj
        exact absurd (List.find?_eq_none.mp hf r hr) (by simp [e])
      rw [if_neg (fun (h : j = i ∧ i ∈ s.resources ∧ i ≠ s.storage) =>
        hnj (by rw [h.1]; exact h.2.1))]
      rfl
    | some r =>
      have hrj : r.resource = j := Subtype.ext (by simpa using List.find?_some hf)
      show (replaceRead i etag g r).graph = _
      unfold replaceRead
      by_cases h : j = i
      · have hi : i ∈ s.resources :=
          (mem_resources s i).mpr ⟨r, List.mem_of_find?_eq_some hf, hrj.trans h⟩
        rw [if_pos (hrj.trans h), if_pos ⟨h, hi, fun e => hjs (h.trans e)⟩]
      · rw [if_neg (fun e => h (hrj.symm.trans e)), if_neg (fun hc => h hc.1)]

/-- **Replacing one document's representation changes exactly one graph.**
The default graph is the same, and the named graphs are those of the view
before the change with the graph named by `i` replaced by `g`, when `i` is a
document name (a read IRI that is not the storage description IRI). The
table-of-contents graph and the linkset graphs do not change. Since the names
are distinct (`view_names_nodup`), at most one entry is named `i`. -/
theorem view_replace (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (view (s.replace i etag g)).default = (view s).default ∧
      (view (s.replace i etag g)).named =
        (view s).named.map (fun ng =>
          if ng.name = .iri i ∧ i ∈ s.resources ∧ i ≠ s.storage then ⟨ng.name, g⟩ else ng) := by
  refine ⟨rfl, ?_⟩
  show (s.replace i etag g).names.map (fun j => (⟨.iri j, (s.replace i etag g).graphFor j⟩ : NamedGraph)) =
    (s.names.map (fun j => (⟨.iri j, s.graphFor j⟩ : NamedGraph))).map _
  rw [replace_names, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, replace_graphFor]
  by_cases h : j = i ∧ i ∈ s.resources ∧ i ≠ s.storage
  · rw [if_pos h, if_pos ⟨by rw [h.1], h.2⟩]
  · rw [if_neg h, if_neg (fun hc => h ⟨Subject.iri.inj hc.1, hc.2⟩)]

/-- The same, per name: the graph named `i` is `g` (when `i` is a document
name), and every other name has the graph it had. -/
theorem view_replace_lookup (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (i ∈ s.resources → i ≠ s.storage →
        (view (s.replace i etag g)).lookupNamed (.iri i) = some g) ∧
      ∀ n, n ≠ .iri i → (view (s.replace i etag g)).lookupNamed n = (view s).lookupNamed n := by
  constructor
  · intro hi hs
    obtain ⟨r, hr, e⟩ := (mem_resources s i).mp hi
    have hn : i ∈ (s.replace i etag g).names := by
      rw [replace_names]
      exact (mem_names s _).mpr (Or.inr (Or.inl ⟨r, hr, e⟩))
    rw [view_lookup_name _ i hn, replace_graphFor, if_pos ⟨rfl, hi, hs⟩]
  · intro n hn
    unfold Dataset.lookupNamed
    rw [(view_replace s i etag g).2, List.find?_map]
    have hp : ((fun ng : NamedGraph => ng.name == n) ∘
        (fun ng : NamedGraph =>
          if ng.name = .iri i ∧ i ∈ s.resources ∧ i ≠ s.storage then (⟨ng.name, g⟩ : NamedGraph)
          else ng)) =
        (fun ng => ng.name == n) := by
      funext ng
      by_cases h : ng.name = .iri i ∧ i ∈ s.resources ∧ i ≠ s.storage <;> simp [h]
    rw [hp]
    cases hf : (view s).named.find? (fun ng => ng.name == n) with
    | none => rfl
    | some ng =>
      have hng : ng.name = n := by simpa using List.find?_some hf
      have : ¬ (ng.name = .iri i ∧ i ∈ s.resources ∧ i ≠ s.storage) :=
        fun h => hn (hng.symm.trans h.1)
      simp [this]

#print axioms resources_nodup
#print axioms mem_resources
#print axioms names_nodup
#print axioms mem_names
#print axioms view_names
#print axioms view_names_nodup
#print axioms view_mem_names
#print axioms view_toc_first
#print axioms view_lookup_toc
#print axioms view_lookup
#print axioms view_lookup_linkset
#print axioms view_replace
#print axioms view_replace_lookup

end L4Factoidal.LWS.DatasetView
