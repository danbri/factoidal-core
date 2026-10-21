/-
L4Factoidal.LWS.TypeIndex — the derived index behind the Type Index and Type
Search services of the LWS Search and Type Index Services draft, kept up to
date by the store itself. https://github.com/danbri/factoidal/issues/912

Source: "LWS Search and Type Index Services" (lws10-index), W3C Linked Web
Storage Working Group editor's draft, "an unofficial proposal", read
2026-10-21 at w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(`lws10-index/index.html`; the implementations page names it
https://w3c.github.io/lws-protocol/lws10-searchindex). Statements this module
decides, verbatim:

* §Type and Relation Derivation: "servers SHOULD derive resource types from
  HTTP Link headers provided by the client during resource creation or
  modification, combined with the server's intrinsic knowledge of the
  resource's state (such as native LWS classes like
  https://www.w3.org/ns/lws#Container)." — `entryFacts`: the LWS class of
  the resource's kind, and every declared `type` link (`Linkset.declaredType`).
* "Servers MAY additionally derive types from the resource representation
  itself when they are able to parse it. [...] When a server enriches the
  type index from resource content, the types it surfaces MUST be treated
  identically to those derived from Link headers for the purposes of
  indexing, search, and authorization filtering." — `contentTypes`: the
  `rdf:type` objects the Turtle content states of the resource itself; they
  become facts of the same shape as a link's.
* "Type and indexed-relation membership in these services MAY be eventually
  consistent. [...] a server SHOULD reflect the change within a bounded,
  implementation-defined interval" — this index is never stale: it is
  updated inside every `put` and `remove` of the store (`IndexedStore`), so
  the interval is zero.
* §QUERY: "A server MAY additionally index other descriptive link
  relations. [...] Relation targets are derived by the server in the same way
  as types (HTTP Link headers, server-intrinsic state, or parsed content) and
  all sources MUST be treated identically." and "Only descriptive relations
  are eligible for indexing; servers MUST NOT index structural or protocol
  relations." — `linkFact`: every client link whose relation is not in
  `structuralRels`.
* §Security and Authorization: "A server MAY maintain a derived index for
  performance, but it MUST apply current authorization as a filter over that
  index on every request." — this module holds no access decision; the
  services filter its answers per request (`L4Factoidal.LWS.Search`).

How the index is kept correct. `IndexedStore S L` is a `Store` whose state
`IxState` holds the backend's state, the index, and a PROOF (`IndexOk`) that
the index describes the backend's resources: for every path its facts are
`entryFacts` of the resource there, and a path is in the set of a fact
exactly when the fact is among its facts. `put`, `remove` and `tick` each
build the next proof from the backend's `StoreLaws`, so every value of
`IxState` satisfies the invariant, and in particular every state `step`
reaches through this store (`Operations.step` changes the store only
through `put`, `remove` and `tick`). No frame theorem about `step` is
needed, and a later change to `step` cannot break the index.

Costs. A `put` or `remove` updates the sets of the facts of one path: the
old facts (kept in `byPath`, so a body is never parsed twice) and the new
ones. A Turtle body is parsed once per write, up to `contentTypeLimit`
bytes. `rebuildEntries` builds the index from a list of entries in one pass
(linear in the number of entries and their facts); a storage loaded from a
snapshot is indexed that way (theorem `rebuildEntries_ok`).

Server choices, each stated once:

* Content types are read from `text/turtle` bodies of at most
  `contentTypeLimit` bytes (1 MiB); larger bodies and other media types
  contribute no content type. The draft lets a server parse content or not
  ("servers are not required to parse resource content"); the bound keeps
  one write's cost bounded, as §Security Considerations ("Resource
  Exhaustion") asks.
* A link target that is a relative reference is resolved against the
  resource's IRI (RFC 3986 §5); a fact always holds an absolute IRI.
* Relation names are compared as RFC 8288 §2.1.1 says: a registered
  relation type in lower case, an extension relation (a URI) exactly.
* Auxiliary resources (ACL and metadata resources, linksets) have no facts:
  the services describe "the resources within a storage", and their objects
  are containers and data resources.
-/
import Std.Data.HashMap
import Std.Data.HashSet
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Linkset
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.LWS

open Std

/-! ## Facts -/

/-- One indexed statement about a resource: a relation and a target IRI.
A type is the relation `type`. -/
abbrev Fact := String × String

/-- The relation that holds types. -/
def typeRel : String := "type"

/-- `rdf:type`. -/
def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- The two native LWS classes, which every container and data resource
bears (lws10-index §QUERY: "The native LWS classes
https://www.w3.org/ns/lws#DataResource and https://www.w3.org/ns/lws#Container
are ordinary type values"). -/
def nativeClasses : List String := [lwsContainerType, lwsDataResourceType]

/-- The native class of a resource kind. -/
def classOf (k : ResourceKind) : String :=
  if k.isContainer then lwsContainerType else lwsDataResourceType

/-- An RFC 8288 relation name as it is compared: an extension relation (an
absolute URI) as written, a registered relation type in lower case. -/
def normRel (r : String) : String := if absoluteUri r then r else r.toLower

/-- The structural and protocol relations, which are never indexed
(lws10-index §QUERY: "servers MUST NOT index structural or protocol
relations"): the server-managed relations of the core, and the registered
navigation and service relations. -/
def structuralRels : List String :=
  serverManagedRels ++
  [ "acl", "self", "first", "last", "next", "prev", "previous", "edit", "edit-media"
  , "service", "service-desc", "service-doc", "service-meta"
  , "http://www.w3.org/ns/ldp#constrainedBy", "http://www.w3.org/ns/ldp#inbox"
  , "http://www.w3.org/ns/solid/terms#storageDescription"
  , "http://www.w3.org/ns/pim/space#storage" ]

/-- Is a (normalised) relation one this server indexes? -/
def indexedRel (r : String) : Bool := !structuralRels.contains r

/-- A link target as an absolute IRI: resolved against the resource's IRI
when it is a relative reference. -/
def resolveRef (resIri t : String) : String :=
  if absoluteUri t then t else Syntax.resolveIri resIri t

/-- The fact a client link gives, if any: a declared type, or an indexed
relation and its target. A `type` link naming a native class gives none (the
native class comes from the kind). -/
def linkFact (resIri : String) (l : Link) : Option Fact :=
  let r := normRel l.rel
  let t := resolveRef resIri l.target
  if r == typeRel then (if nativeTypeTargets.contains t then none else some (typeRel, t))
  else if indexedRel r then some (r, t) else none

/-- The largest body whose types are read from its content. -/
def contentTypeLimit : Nat := 1048576

/-- The types the Turtle content of a data resource states of the resource
itself: the IRI objects of its `rdf:type` triples whose subject is the
resource's IRI, the body read with that IRI as its base. A body that does
not parse, a body above `contentTypeLimit` bytes and any other media type
give none. -/
def contentTypes (resIri : String) (e : Entry) : List String :=
  if e.kind.isContainer || baseMedia e.contentType != "text/turtle" ||
     e.body.size > contentTypeLimit then []
  else
    match Syntax.parseTurtleText e.text (some resIri) with
    | .error _ => []
    | .ok g => g.filterMap (fun t =>
        match t.s, t.o with
        | .iri s, .iri o =>
            if s.val == resIri && t.p.val == rdfTypeIri && !nativeTypeTargets.contains o.val
            then some o.val else none
        | _, _ => none)

/-- The facts of one stored resource: its native class first, then its
declared types and indexed relations from its links, then the types its
content states. An auxiliary resource has none. -/
def entryFacts (baseIri : String) (e : Entry) : List Fact :=
  if e.kind.isAuxiliary then []
  else
    let resIri := iriOfPath baseIri e.path
    ((typeRel, classOf e.kind) :: e.links.filterMap (linkFact resIri)) ++
      (contentTypes resIri e).map (fun t => (typeRel, t))

/-- The facts at a path, from what the store holds there. -/
def factsAt (baseIri : String) : Option Entry → List Fact
  | some e => entryFacts baseIri e
  | none => []

theorem entryFacts_aux {b : String} {e : Entry} (h : e.kind.isAuxiliary = true) :
    entryFacts b e = [] := by
  simp [entryFacts, h]

theorem class_mem_entryFacts {b : String} {e : Entry} (h : e.kind.isAuxiliary = false) :
    (typeRel, classOf e.kind) ∈ entryFacts b e := by
  simp [entryFacts, h]

/-- A path with a fact holds a resource that is not auxiliary. -/
theorem some_of_mem_factsAt {b : String} {o : Option Entry} {f : Fact}
    (h : f ∈ factsAt b o) : ∃ e, o = some e ∧ e.kind.isAuxiliary = false := by
  cases o with
  | none => simp [factsAt] at h
  | some e =>
      refine ⟨e, rfl, ?_⟩
      cases ha : e.kind.isAuxiliary
      · rfl
      · simp [factsAt, entryFacts_aux ha] at h

theorem classOf_mem_nativeClasses (k : ResourceKind) : classOf k ∈ nativeClasses := by
  unfold classOf nativeClasses
  split <;> simp

/-! ## The index -/

/-- The derived index: the facts of every path, and for every fact the set
of paths that have it. -/
structure IndexData where
  byPath : HashMap String (List Fact) := {}
  byFact : HashMap Fact (HashSet String) := {}

instance : Inhabited IndexData := ⟨{}⟩

/-- Remove `p` from the set of each fact in `fs`. One loop step per fact. -/
def detachAll (m : HashMap Fact (HashSet String)) (p : String) :
    List Fact → HashMap Fact (HashSet String)
  | [] => m
  | f :: fs => detachAll (m.insert f ((m.getD f ∅).erase p)) p fs

/-- Add `p` to the set of each fact in `fs`. One loop step per fact. -/
def attachAll (m : HashMap Fact (HashSet String)) (p : String) :
    List Fact → HashMap Fact (HashSet String)
  | [] => m
  | f :: fs => attachAll (m.insert f ((m.getD f ∅).insert p)) p fs

/-- Replace the facts of path `p` by `fs`. An empty `fs` forgets the path. -/
def IndexData.set (ix : IndexData) (p : String) (fs : List Fact) : IndexData :=
  { byPath := if fs.isEmpty then ix.byPath.erase p else ix.byPath.insert p fs
    byFact := attachAll (detachAll ix.byFact p (ix.byPath.getD p [])) p fs }

/-- The paths that have fact `f`. -/
def IndexData.pathsOf (ix : IndexData) (f : Fact) : HashSet String := ix.byFact.getD f ∅

theorem mem_detachAll (m : HashMap Fact (HashSet String)) (p q : String) (f : Fact)
    (fs : List Fact) :
    q ∈ (detachAll m p fs).getD f ∅ ↔ q ∈ m.getD f ∅ ∧ (f ∈ fs → q ≠ p) := by
  induction fs generalizing m with
  | nil => simp [detachAll]
  | cons g gs ih =>
      simp only [detachAll]
      rw [ih, HashMap.getD_insert]
      by_cases h : g = f
      · subst h
        simp only [beq_self_eq_true, if_true, HashSet.mem_erase, List.mem_cons, true_or,
          forall_const]
        constructor
        · rintro ⟨⟨hpq, hq⟩, _⟩
          refine ⟨hq, ?_⟩
          intro hqp
          subst hqp
          simp at hpq
        · rintro ⟨hq, hne⟩
          refine ⟨⟨?_, hq⟩, fun _ => hne⟩
          simpa [beq_eq_false_iff_ne] using fun h' => hne h'.symm
      · have hb : (g == f) = false := by simpa [beq_eq_false_iff_ne] using h
        have hfg : f ≠ g := fun h' => h h'.symm
        simp only [hb, Bool.false_eq_true, if_false, List.mem_cons, hfg, false_or]

theorem mem_attachAll (m : HashMap Fact (HashSet String)) (p q : String) (f : Fact)
    (fs : List Fact) :
    q ∈ (attachAll m p fs).getD f ∅ ↔ q ∈ m.getD f ∅ ∨ (f ∈ fs ∧ q = p) := by
  induction fs generalizing m with
  | nil => simp [attachAll]
  | cons g gs ih =>
      simp only [attachAll]
      rw [ih, HashMap.getD_insert]
      by_cases h : g = f
      · subst h
        simp only [beq_self_eq_true, if_true, HashSet.mem_insert, List.mem_cons, true_or,
          true_and, beq_iff_eq]
        constructor
        · rintro ((hpq | hq) | ⟨_, hqp⟩)
          · exact Or.inr hpq.symm
          · exact Or.inl hq
          · exact Or.inr hqp
        · rintro (hq | hqp)
          · exact Or.inl (Or.inr hq)
          · exact Or.inl (Or.inl hqp.symm)
      · have hb : (g == f) = false := by simpa [beq_eq_false_iff_ne] using h
        have hfg : f ≠ g := fun h' => h h'.symm
        simp only [hb, Bool.false_eq_true, if_false, List.mem_cons, hfg, false_or]

/-- The invariant: the index describes the resources `look` resolves.
`byPath` holds the facts of every path, and a path is in the set of a fact
exactly when that fact is one of its facts. -/
structure IndexOk (baseIri : String) (look : String → Option Entry) (ix : IndexData) : Prop where
  byPath : ∀ p, ix.byPath.getD p [] = factsAt baseIri (look p)
  byFact : ∀ f p, p ∈ ix.byFact.getD f ∅ ↔ f ∈ ix.byPath.getD p []

/-- What the invariant says of one path and one fact. -/
theorem IndexOk.mem_iff {b : String} {look : String → Option Entry} {ix : IndexData}
    (h : IndexOk b look ix) (f : Fact) (p : String) :
    p ∈ ix.pathsOf f ↔ f ∈ factsAt b (look p) := by
  unfold IndexData.pathsOf
  rw [h.byFact, h.byPath]

/-- The empty index describes the empty store. -/
theorem IndexOk.empty (b : String) : IndexOk b (fun _ => none) {} where
  byPath := by intro p; simp [factsAt]
  byFact := by intro f p; simp

theorem getD_byPath_set (ix : IndexData) (p q : String) (fs : List Fact) :
    (ix.set p fs).byPath.getD q [] = if p = q then fs else ix.byPath.getD q [] := by
  unfold IndexData.set
  by_cases he : fs.isEmpty = true
  · simp only [he, if_true, HashMap.getD_erase]
    have : fs = [] := List.isEmpty_iff.mp he
    by_cases hpq : p = q
    · simp [hpq, this]
    · simp [hpq]
  · simp only [he, Bool.false_eq_true, if_false, HashMap.getD_insert]
    by_cases hpq : p = q
    · simp [hpq]
    · simp [hpq]

/-- **Replacing the facts of one path keeps the invariant.** If `look'`
differs from `look` only at `p`, setting the facts of `p` to those of
`look' p` turns an index of `look` into an index of `look'`. -/
theorem IndexOk.set {b : String} {look look' : String → Option Entry} {ix : IndexData}
    (h : IndexOk b look ix) (p : String) (hother : ∀ q, q ≠ p → look' q = look q) :
    IndexOk b look' (ix.set p (factsAt b (look' p))) where
  byPath := by
    intro q
    rw [getD_byPath_set]
    by_cases hpq : p = q
    · subst hpq; simp
    · have hq : q ≠ p := fun h' => hpq h'.symm
      simp only [hpq, if_false, h.byPath, hother q hq]
  byFact := by
    intro f q
    rw [getD_byPath_set]
    show q ∈ (attachAll (detachAll ix.byFact p (ix.byPath.getD p [])) p
      (factsAt b (look' p))).getD f ∅ ↔ _
    rw [mem_attachAll, mem_detachAll, h.byFact]
    by_cases hpq : p = q
    · subst hpq
      simp only [if_true]
      constructor
      · rintro (⟨hf, hne⟩ | ⟨hf, _⟩)
        · exact absurd rfl (hne hf)
        · exact hf
      · intro hf; exact Or.inr ⟨hf, trivial⟩
    · have hq : q ≠ p := fun h' => hpq h'.symm
      simp only [hpq, if_false]
      constructor
      · rintro (⟨hf, _⟩ | ⟨_, hqp⟩)
        · exact hf
        · exact absurd hqp hq
      · intro hf; exact Or.inl ⟨hf, fun _ => hq⟩

/-! ## The indexed store -/

/-- A backend state with its index and the proof that the index describes
it. -/
structure IxState {σ : Type} (S : Store σ) where
  base : σ
  /-- The storage's base IRI, which resolves `<>` in content and relative
  link targets. -/
  baseIri : String
  ix : IndexData
  ok : IndexOk baseIri (S.lookup base) ix

variable {σ : Type}

/-- The store that maintains the index: every `put` and `remove` of the
backend updates the facts of the one path it touches. -/
def IndexedStore (S : Store σ) (L : StoreLaws S) : Store (IxState S) where
  lookup s p := S.lookup s.base p
  put s e :=
    { base := S.put s.base e, baseIri := s.baseIri
      ix := s.ix.set e.path (entryFacts s.baseIri e)
      ok := by
        have h := s.ok.set e.path (look' := S.lookup (S.put s.base e))
          (fun q hq => L.lookupPutOther s.base e q hq)
        rw [L.lookupPutSame] at h
        exact h }
  remove s p :=
    { base := S.remove s.base p, baseIri := s.baseIri
      ix := s.ix.set p []
      ok := by
        have h := s.ok.set p (look' := S.lookup (S.remove s.base p))
          (fun q hq => L.lookupRemoveOther s.base p q hq)
        rw [L.lookupRemoveSame] at h
        exact h }
  paths s := S.paths s.base
  now s := S.now s.base
  tick s :=
    { base := S.tick s.base, baseIri := s.baseIri, ix := s.ix
      ok := by
        have : S.lookup (S.tick s.base) = S.lookup s.base := funext (L.lookupTick s.base)
        rw [this]
        exact s.ok }

/-- The indexed store satisfies every law of the backend. -/
theorem indexedStoreLaws (S : Store σ) (L : StoreLaws S) : StoreLaws (IndexedStore S L) where
  lookupPutSame := fun s e => L.lookupPutSame s.base e
  lookupPutOther := fun s e p h => L.lookupPutOther s.base e p h
  lookupRemoveSame := fun s p => L.lookupRemoveSame s.base p
  lookupRemoveOther := fun s p q h => L.lookupRemoveOther s.base p q h
  pathsLookup := fun s p => L.pathsLookup s.base p
  nowTick := fun s => L.nowTick s.base
  lookupTick := fun s p => L.lookupTick s.base p

/-- The invariant of every indexed state, in terms of the indexed store. -/
theorem IxState.mem_iff {S : Store σ} (L : StoreLaws S) (st : IxState S) (f : Fact) (p : String) :
    p ∈ st.ix.pathsOf f ↔ f ∈ factsAt st.baseIri ((IndexedStore S L).lookup st p) :=
  st.ok.mem_iff f p

/-! ## Building the index in one pass -/

/-- The index of a list of entries, where the first entry at a path is the
one that counts (`List.find?`). One `set` per entry, in a loop over the
reversed list, so the first entry is set last. -/
def rebuildEntries (b : String) (es : List Entry) : IndexData :=
  es.reverse.foldl (fun ix e => ix.set e.path (entryFacts b e)) {}

/-- **The rebuilt index describes the entries.** -/
theorem rebuildEntries_ok (b : String) (es : List Entry) :
    IndexOk b (fun p => es.find? (fun e => e.path == p)) (rebuildEntries b es) := by
  unfold rebuildEntries
  rw [List.foldl_reverse]
  induction es with
  | nil => simpa using IndexOk.empty b
  | cons e es ih =>
      simp only [List.foldr_cons]
      have h := ih.set e.path (look' := fun p => (e :: es).find? (fun x => x.path == p))
        (fun q hq => by
          have : (e.path == q) = false := by simpa [beq_eq_false_iff_ne] using fun h' => hq h'.symm
          simp [this])
      simp only [List.find?_cons, beq_self_eq_true] at h
      exact h

/-- An indexed state of the reference store, built from its entries. -/
def IxState.ofMem (b : String) (m : MemState) : IxState MemStore :=
  { base := m, baseIri := b, ix := rebuildEntries b m.entries
    ok := rebuildEntries_ok b m.entries }

/-- Set the clock of an indexed reference state; no resource changes. -/
def IxState.withClock (s : IxState MemStore) (t : Nat) : IxState MemStore :=
  { s with base := { s.base with clock := t }, ok := s.ok }

/-! ## Checks -/

private def base : String := "http://example.org/"

private def person : Entry :=
  { path := "/p", kind := .dataResource, contentType := "text/turtle; charset=utf-8",
    body := textBytes "<> a <https://schema.org/Event> . <other> a <https://schema.org/Thing> .",
    mtime := 0,
    links := [ { target := "https://schema.org/Person", rel := "type" }
             , { target := "#shape", rel := "describedby" }
             , { target := "http://example.org/", rel := "up" } ] }

-- The native class first, the declared type, the indexed relation resolved
-- against the resource, then the content type of the resource itself; `up`
-- is structural, and the content's statement about another subject is not
-- a type of this resource.
#guard entryFacts base person ==
  [ (typeRel, lwsDataResourceType), (typeRel, "https://schema.org/Person")
  , ("describedby", "http://example.org/p#shape"), (typeRel, "https://schema.org/Event") ]
-- An auxiliary resource has no facts; a container has its class.
#guard entryFacts base { person with kind := .metadataResource } == []
#guard entryFacts base { person with path := "/c/", kind := .container, links := [] } ==
  [(typeRel, lwsContainerType)]
-- A type link naming a native class gives no fact; registered relations
-- compare in lower case, extension relations exactly.
#guard linkFact "http://example.org/p" { target := lwsContainerType, rel := "type" } == none
#guard linkFact "http://example.org/p" { target := "https://ex.org/s", rel := "DescribedBy" } ==
  some ("describedby", "https://ex.org/s")
#guard linkFact "http://example.org/p" { target := "https://ex.org/s", rel := "https://ex.org/Rel" } ==
  some ("https://ex.org/Rel", "https://ex.org/s")
#guard linkFact "http://example.org/p" { target := "https://ex.org/s", rel := "acl" } == none
-- Content of another media type, or above the limit, gives no type.
#guard contentTypes "http://example.org/p" { person with contentType := "text/plain" } == []
#guard contentTypes "http://example.org/p"
  { person with body := textBytes ("<> a <https://schema.org/Event> .\n#" ++
      String.ofList (List.replicate contentTypeLimit 'x')) } == []
-- Content that does not parse gives no type.
#guard contentTypes "http://example.org/p" { person with body := textBytes "<> a" } == []

-- The index of three entries; the first entry at a path counts.
private def ixOf (es : List Entry) : IndexData := rebuildEntries base es

#guard ((ixOf [person, { person with links := [] }]).pathsOf (typeRel, "https://schema.org/Person")).contains "/p"
#guard !((ixOf [{ person with links := [] }, person]).pathsOf (typeRel, "https://schema.org/Person")).contains "/p"
-- Removing the facts of a path removes it from every set.
#guard !(((ixOf [person]).set "/p" []).pathsOf (typeRel, lwsDataResourceType)).contains "/p"
#guard ((ixOf [person]).set "/p" []).byPath.isEmpty

end L4Factoidal.LWS
