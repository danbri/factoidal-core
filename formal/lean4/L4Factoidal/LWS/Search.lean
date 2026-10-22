/-
L4Factoidal.LWS.Search — the Type Index Service and the Type Search Service
of the LWS Search and Type Index Services draft, decided in Lean.
https://github.com/danbri/factoidal/issues/912

Source: "LWS Search and Type Index Services" (lws10-index), W3C Linked Web
Storage Working Group editor's draft, "an unofficial proposal", read
2026-10-21 at w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc.
The index it reads is `L4Factoidal.LWS.TypeIndex`. Statements this module
decides, verbatim, with the definition that decides each:

§Discovery
* "A storage that supports one of these services MUST advertise it with a
  service object in the service array of its storage description resource:
  the entry for the Type Index Service MUST have a type equal to
  TypeIndexService, and the entry for the Type Search Service MUST have a type
  equal to TypeSearchService." and "Each service object MUST include a
  serviceEndpoint property" — `Binding.storageDescription` (`typeIndex`).
* "the set of additional indexed relations a server supports is deliberately
  not enumerated there or anywhere else" — no response names them.

§GET [TypeIndexService]
* "Returns a paginated TypeIndex as application/lws+json, following the
  standard LWS pagination model [...] page URIs are conveyed in Link
  headers [...] The body lists the unique types of resources that currently
  exist within the storage and that the authenticated user is authorized to
  see." — `typeIndexStep`, `visibleTypes` (theorem
  `visibleTypes_eq_specTypes`).

§QUERY [TypeSearchService]
* "The query format is identified by the request's Content-Type header field,
  which MUST be present" and "Every server MUST support the
  application/lws-query+json filter format" — `searchStep`.
* "A member whose name begins with @ (a JSON-LD keyword such as @context) MUST
  be ignored" — `parseFilter`.
* "A server SHOULD advertise the query formats it accepts using the
  Accept-Query response header field" — OPTIONS and every search answer.
* "The type key is OPTIONAL and selects resources by their rdf:type [...] Its
  value is an array whose elements are combined with logical AND; each element
  is either a single type IRI [RFC3987] or an array of type IRIs combined with
  logical OR." and "A request whose body has no type key and no relation keys
  (or all of whose keys have values of empty arrays) matches all resources
  visible to the client." — `Filter`, `selects`.
* "A type filter always denotes the type the matched resource itself bears"
  and the native classes "are ordinary type values" — `TypeIndex.entryFacts`.
* "a server MUST NOT extend this grammar", "A type IRI that matches no
  resource yields no results and MUST NOT be treated as an error, and
  duplicate groups MUST be ignored. An empty group [...] MUST be rejected with
  400 (Bad Request)" and "A filter key whose entire value is an empty array
  expresses no constraint" — `parseFilter`.
* "Such a relation is filtered by using the relation itself as a key alongside
  type [...] with exactly the same conjunctive-normal-form semantics as type"
  and "A relation the server does not index, like a target value that matches
  nothing, yields no results for that constraint: this MUST NOT be treated as
  an error, and the two cases MUST be indistinguishable to the client." — a
  relation key is a `Group` like `type`; an unindexed relation has no facts,
  so the answer is the same empty page.
* "A successful search returns 200 (OK). The default response is an
  application/lws+json ContainerPage" and "if it can satisfy none of the media
  types the request finds acceptable, it responds 406" — `resultMedia`.
* "Each item in a ContainerPage result MUST carry at least the matched
  resource's id and its type" — `resultItem`.
* "the result set is paginated according to the standard LWS pagination
  model" — `searchPage`; the page URIs carry the filter (`filterToken`), so a
  page is computed again, and authorized again, on every request.
* Content-Location: "this specification does not define such a resource";
  by default this server sends none. With `Config.searchResults` on, an
  ANTICIPATORY AND UNSTABLE results resource is named
  (`L4Factoidal.LWS.SearchResults`, https://github.com/danbri/factoidal/issues/922).

§Errors
* not well-formed body, `type` not an array, an element "neither a string
  nor a non-empty array of strings" — 400; unsupported query format — 415
  "and such a response SHOULD include an Accept-Query header field"; missing
  Content-Type — 400; Accept excluding every format — 406; a value that "does
  not match the IRI production of [RFC3987]" — 400 (`filterIriValid`); "A
  filter that is well-formed but exceeds the complexity a server chooses to
  support [...] MUST be rejected with 422" and "A server MUST NOT silently
  truncate" — `maxFilterTerms`; "A pagination reference [...] that the server
  no longer recognizes [...] MUST result in 404 (Not Found) or 410 (Gone)" —
  404. "A server that negotiates the response representation on Accept [...]
  MUST list Accept in Vary" — every answer.

§Security and Authorization
* "Responses from the TypeIndexService (a GET) and the TypeSearchService (a
  QUERY) include only types and resource URIs that the authenticated client is
  explicitly authorized to read." and "Unauthorized entries MUST be omitted
  entirely." — `searchAnswer` (theorem `searchAnswer_authorized`),
  `visibleTypes`.
* "Any count a response exposes, including totalItems, MUST be computed over
  this client-specific, authorization-filtered view" — `totalItems` is the
  length of the filtered answer.
* "Authorization filtering MUST be evaluated against the requesting client's
  current access at the time the request is served [...] it MUST apply current
  authorization as a filter over that index on every request." — `canRead` is
  Web Access Control over the state the request is served from
  (`Notifications.wacCanRead`).
* "A server MUST mark such responses so that they are not reused across
  clients (for example with Cache-Control: private or no-store) and MUST vary
  any cached entry on the credential that scopes the result." —
  `Cache-Control: private`, `Vary: accept, authorization`.

Theorems. `ixSearch_eq_specSearch`: for every indexed state, the index answer
is the same list as filtering every path of the store with `selects`
(soundness and completeness). `searchAnswer_eq_spec` adds authorization;
`searchAnswer_authorized` and `searchPagePaths_authorized`: no answer names a
path the agent cannot read. `visibleTypes_eq_specTypes`: the type index is
the set of types of the resources the agent may read. `search_after_step`
states the first for the state after any `Operations.step`.

Server choices: the endpoints (`Binding.typeIndexPath`,
`Binding.typeSearchPath`); `maxFilterTerms` = 64 IRIs; result order is
increasing path order (`orderPaths`), type index order increasing IRI order;
page size `Config.pageSize`; an anonymous client is answered with what the
public may read.
-/
import L4Factoidal.LWS.TypeIndex
import L4Factoidal.LWS.Notifications
import L4Factoidal.JOSE.Base64Url

namespace L4Factoidal.LWS.Search

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)
open Std

variable {σ : Type}

/-! ## Filters -/

/-- One group of a filter: a relation and the targets it ORs. -/
abbrev Group := String × List String

/-- A filter: groups that are ANDed (conjunctive normal form). -/
abbrev Filter := List Group

/-- Does a resource with facts `fs` satisfy the group? -/
def groupHolds (fs : List Fact) (g : Group) : Bool := g.2.any (fun t => fs.contains (g.1, t))

/-- Does a resource with facts `fs` satisfy every group? -/
def filterHolds (gs : Filter) (fs : List Fact) : Bool := gs.all (groupHolds fs)

/-- **The specification**: does the filter select what the store holds at a
path? It must be a container or data resource whose facts satisfy every
group. -/
def selects (b : String) (gs : Filter) : Option Entry → Bool
  | some e => indexable e && filterHolds gs (entryFacts b e)
  | none => false

/-- The specified answer: every path of the store the filter selects, in
increasing path order. -/
def specSearch (S : Store σ) (b : String) (gs : Filter) (st : σ) : List String :=
  orderPaths ((S.paths st).filter (fun p => selects b gs (S.lookup st p)))

/-! ## Reading a filter document (application/lws-query+json) -/

/-- The most IRIs a filter may hold; a larger filter is refused with 422. -/
def maxFilterTerms : Nat := 64

/-- RFC 3987 `IRI`, as this server checks it: an absolute IRI (a scheme, then
no character RFC 3986 excludes), with at most one fragment. -/
def filterIriValid (s : String) : Bool := absoluteUri s && (s.splitOn "#").length ≤ 2

/-- The relation a filter key names. -/
def relKey (k : String) : String := if k == typeRel then typeRel else normRel k

/-- The targets of one element of a key's value. -/
def parseGroupElem (k : String) : Json → Except (Nat × String) (List String)
  | .string s =>
      if filterIriValid s then .ok [s] else .error (400, s!"{s} in {k} is not an absolute IRI")
  | .array [] => .error (400, s!"an empty group in {k} matches nothing and is refused")
  | .array xs => xs.mapM (fun x => match x with
      | .string s =>
          if filterIriValid s then .ok s else .error (400, s!"{s} in {k} is not an absolute IRI")
      | _ => .error (400, s!"a group in {k} holds a value that is not a string"))
  | _ => .error (400, s!"an element of {k} is neither a string nor a non-empty array of strings")

/-- Read a filter document: 400 for a document the grammar refuses, 422 for
more than `maxFilterTerms` IRIs. Members whose names begin with `@` are
ignored; each group's targets are kept in increasing order, once; repeated
groups are kept once. -/
def parseFilter (j : Json) : Except (Nat × String) Filter := do
  let fields ← match j with
    | .object fs => pure fs
    | _ => throw (400, "a filter document is a JSON object")
  let mut groups : Array Group := #[]
  for (k, v) in fields do
    if k.startsWith "@" then continue
    match v with
    | .array elems =>
        for el in elems do
          let alts ← parseGroupElem k el
          groups := groups.push (relKey k, orderPaths alts)
    | _ => throw (400, s!"the value of {k} is not an array")
  let gs := groups.toList.eraseDups
  if gs.foldl (fun n g => n + g.2.length) 0 > maxFilterTerms then
    throw (422, s!"the filter holds more than {maxFilterTerms} IRIs")
  return gs

/-- A filter as a filter document again (one key per relation). -/
def filterJson (gs : Filter) : Json :=
  let rels := (gs.map (·.1)).eraseDups
  .object (rels.map (fun r =>
    (r, .array ((gs.filter (·.1 == r)).map (fun g => Json.array (g.2.map Json.string))))))

/-- The opaque page reference of a filter: its document, base64url. -/
def filterToken (gs : Filter) : String :=
  JOSE.Base64Url.encode (toStringCompact (filterJson gs)).toUTF8

/-- The filter a page reference names, if it names one. -/
def filterOfToken? (t : String) : Option Filter :=
  match (JOSE.Base64Url.decode t).bind String.fromUTF8? with
  | none => none
  | some text => match parseJson text with
    | .error _ => none
    | .ok j => (parseFilter j).toOption

/-! ## Answering from the index -/

/-- Is `p` in the set of some target of the group? -/
def groupMember (ix : IndexData) (p : String) (g : Group) : Bool :=
  g.2.any (fun t => (ix.pathsOf (g.1, t)).contains p)

/-- The paths in the sets of the group's targets. -/
def groupCandidates (ix : IndexData) (g : Group) : List String :=
  g.2.flatMap (fun t => (ix.pathsOf (g.1, t)).toList)

/-- The number of paths in the sets of the group's targets. -/
def groupCost (ix : IndexData) (g : Group) : Nat :=
  g.2.foldl (fun n t => n + (ix.pathsOf (g.1, t)).size) 0

/-- The group with the fewest candidates. -/
def smallestGroup (ix : IndexData) (g : Group) : List Group → Group
  | [] => g
  | h :: hs => smallestGroup ix (if groupCost ix h < groupCost ix g then h else g) hs

theorem smallestGroup_mem (ix : IndexData) (g : Group) (hs : List Group) :
    smallestGroup ix g hs ∈ g :: hs := by
  induction hs generalizing g with
  | nil => simp [smallestGroup]
  | cons h hs ih =>
      simp only [smallestGroup]
      by_cases hc : groupCost ix h < groupCost ix g
      · simp only [hc, if_true]
        have := ih h
        simp only [List.mem_cons] at this ⊢
        rcases this with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · simp only [hc, if_false]
        have := ih g
        simp only [List.mem_cons] at this ⊢
        rcases this with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

/-- The candidates of a filter: the paths of its smallest group, or of the
two native classes when it has no group. Only these are examined. -/
def candidates (ix : IndexData) : Filter → List String
  | [] => groupCandidates ix (typeRel, nativeClasses)
  | g :: rest => groupCandidates ix (smallestGroup ix g rest)

/-- The index answer: the candidates in every group, in increasing order. -/
def ixSearch (ix : IndexData) (gs : Filter) : List String :=
  orderPaths ((candidates ix gs).filter (fun p => gs.all (groupMember ix p)))

theorem contains_iff_mem_facts (fs : List Fact) (f : Fact) : fs.contains f = true ↔ f ∈ fs := by
  simp

theorem groupMember_eq {b : String} {look : String → Option Entry} {ix : IndexData}
    (h : IndexOk b look ix) (p : String) (g : Group) :
    groupMember ix p g = groupHolds (factsAt b (look p)) g := by
  unfold groupMember groupHolds
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, ht, (contains_iff_mem_facts _ _).mpr
      ((h.mem_iff (g.1, t) p).mp (TreeSet.mem_iff_contains.mpr hc))⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, ht, TreeSet.mem_iff_contains.mp
      ((h.mem_iff (g.1, t) p).mpr ((contains_iff_mem_facts _ _).mp hc))⟩

theorem mem_groupCandidates {b : String} {look : String → Option Entry} {ix : IndexData}
    (h : IndexOk b look ix) (p : String) (g : Group) :
    p ∈ groupCandidates ix g ↔ groupHolds (factsAt b (look p)) g = true := by
  unfold groupCandidates groupHolds
  simp only [List.mem_flatMap, TreeSet.mem_toList, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, (contains_iff_mem_facts _ _).mpr ((h.mem_iff (g.1, t) p).mp hp)⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, ht, (h.mem_iff (g.1, t) p).mpr ((contains_iff_mem_facts _ _).mp hc)⟩

/-- `selects` in two parts: a container or data resource, and the groups. -/
theorem selects_iff (b : String) (gs : Filter) (o : Option Entry) :
    selects b gs o = true ↔
      (∃ e, o = some e ∧ indexable e = true) ∧ filterHolds gs (factsAt b o) = true := by
  cases o with
  | none => simp [selects]
  | some e =>
      cases ha : indexable e <;> simp [selects, factsAt, ha]

/-- A group that holds names a fact, so the path holds a resource. -/
theorem some_of_groupHolds {b : String} {o : Option Entry} {g : Group}
    (h : groupHolds (factsAt b o) g = true) : ∃ e, o = some e ∧ indexable e = true := by
  unfold groupHolds at h
  simp only [List.any_eq_true] at h
  obtain ⟨t, _, hc⟩ := h
  exact some_of_mem_factsAt ((contains_iff_mem_facts _ _).mp hc)

/-- **Soundness and completeness of the index answer at one path.** -/
theorem mem_ixSearch {b : String} {look : String → Option Entry} {ix : IndexData}
    (h : IndexOk b look ix) (gs : Filter) (p : String) :
    p ∈ ixSearch ix gs ↔ selects b gs (look p) = true := by
  unfold ixSearch
  rw [mem_orderPaths, List.mem_filter, selects_iff]
  have hall : gs.all (groupMember ix p) = filterHolds gs (factsAt b (look p)) := by
    unfold filterHolds
    induction gs with
    | nil => rfl
    | cons g gs ih => simp [List.all_cons, groupMember_eq h p g, ih]
  rw [hall]
  cases gs with
  | nil =>
      simp only [candidates, mem_groupCandidates h, filterHolds, List.all_nil, and_true]
      constructor
      · intro hg; exact some_of_groupHolds hg
      · rintro ⟨e, he, ha⟩
        unfold groupHolds
        simp only [List.any_eq_true]
        refine ⟨classOf e.kind, classOf_mem_nativeClasses _, ?_⟩
        rw [he]
        exact (contains_iff_mem_facts _ _).mpr (class_mem_entryFacts ha)
  | cons g rest =>
      simp only [candidates, mem_groupCandidates h]
      have hmem := smallestGroup_mem ix g rest
      constructor
      · rintro ⟨hc, hf⟩
        exact ⟨some_of_groupHolds hc, hf⟩
      · rintro ⟨_, hf⟩
        refine ⟨?_, hf⟩
        unfold filterHolds at hf
        exact List.all_eq_true.mp hf _ hmem

/-- **The index answer equals a filter over the store.** For every indexed
state (so for every state `step` reaches through `IndexedStore`), the paths
the index gives are exactly, and in the same order, the paths of the store
whose resource the filter selects. -/
theorem ixSearch_eq_specSearch (S : Store σ) (L : StoreLaws S) (st : IxState S) (gs : Filter) :
    ixSearch st.ix gs = specSearch S st.baseIri gs st.base := by
  unfold specSearch
  conv => lhs; unfold ixSearch
  apply orderPaths_ext
  intro p
  have hm := mem_ixSearch st.ok gs p
  unfold ixSearch at hm
  rw [mem_orderPaths] at hm
  rw [hm, List.mem_filter]
  constructor
  · intro hs
    refine ⟨?_, hs⟩
    obtain ⟨e, he, _⟩ := ((selects_iff _ _ _).mp hs).1
    have hc := L.pathsLookup st.base p
    rw [he] at hc
    simpa using hc
  · exact fun h => h.2

/-! ## Authorization -/

/-- The answer the requesting agent gets: the index answer, filtered by what
it may read now. -/
def searchAnswer (ix : IndexData) (gs : Filter) (canRead : String → Bool) : List String :=
  (ixSearch ix gs).filter canRead

theorem searchAnswer_eq_spec (S : Store σ) (L : StoreLaws S) (st : IxState S) (gs : Filter)
    (canRead : String → Bool) :
    searchAnswer st.ix gs canRead = (specSearch S st.baseIri gs st.base).filter canRead := by
  unfold searchAnswer
  rw [ixSearch_eq_specSearch S L st gs]

/-- **No answer names a resource the agent cannot read.** -/
theorem searchAnswer_authorized {ix : IndexData} {gs : Filter} {canRead : String → Bool}
    {p : String} (h : p ∈ searchAnswer ix gs canRead) : canRead p = true :=
  (List.mem_filter.mp h).2

/-- The answer at one path: a resource of the store, selected, and readable. -/
theorem mem_searchAnswer (S : Store σ) (L : StoreLaws S) (st : IxState S) (gs : Filter)
    (canRead : String → Bool) (p : String) :
    p ∈ searchAnswer st.ix gs canRead ↔
      p ∈ S.paths st.base ∧ selects st.baseIri gs (S.lookup st.base p) = true ∧
        canRead p = true := by
  rw [searchAnswer_eq_spec S L st, List.mem_filter, specSearch, mem_orderPaths, List.mem_filter,
    and_assoc]

/-- The paths of page `n` (from 1) of an answer at page size `k`. -/
def searchPagePaths (ix : IndexData) (gs : Filter) (canRead : String → Bool) (k n : Nat) :
    List String :=
  pageAt (searchAnswer ix gs canRead) k (n - 1)

theorem mem_pageAt {xs : List String} {k i : Nat} {x : String} (h : x ∈ pageAt xs k i) :
    x ∈ xs := by
  unfold pageAt at h
  split at h
  · exact h
  · exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- Every resource on every page of a search is one the agent may read. -/
theorem searchPagePaths_authorized {ix : IndexData} {gs : Filter} {canRead : String → Bool}
    {k n : Nat} {p : String} (h : p ∈ searchPagePaths ix gs canRead k n) : canRead p = true :=
  searchAnswer_authorized (mem_pageAt h)

/-- The index answer after any LWS step through the indexed store is the
filter over the store after that step. -/
theorem search_after_step (S : Store σ) (L : StoreLaws S) (cfg : Config) (r : Request)
    (st : IxState S) (gs : Filter) (canRead : String → Bool) :
    let st' := (step (IndexedStore S L) cfg r st).2
    searchAnswer st'.ix gs canRead = (specSearch S st'.baseIri gs st'.base).filter canRead :=
  searchAnswer_eq_spec S L _ gs canRead

/-! ## The type index -/

/-- The types among some facts. -/
def typesOf (fs : List Fact) : List String :=
  fs.filterMap (fun f => if f.1 == typeRel then some f.2 else none)

theorem mem_typesOf (fs : List Fact) (t : String) : t ∈ typesOf fs ↔ (typeRel, t) ∈ fs := by
  unfold typesOf
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨f, hf, he⟩
    split at he
    · rename_i h1
      simp only [Option.some.injEq] at he
      have : f = (typeRel, t) := by
        cases f; simp only [beq_iff_eq] at h1; simp_all
      rw [← this]; exact hf
    · simp at he
  · intro h
    exact ⟨(typeRel, t), h, by simp⟩

/-- The types the agent may see: those borne by at least one resource it may
read, in increasing order. One pass over the index's facts. -/
def visibleTypes (ix : IndexData) (canRead : String → Bool) : List String :=
  orderPaths (ix.byFact.foldl (fun acc f ps =>
    if f.1 == typeRel && ps.toList.any canRead then f.2 :: acc else acc) [])

/-- The specified type index: the types of every resource the agent may read. -/
def specTypes (S : Store σ) (b : String) (canRead : String → Bool) (st : σ) : List String :=
  orderPaths ((S.paths st).flatMap (fun p =>
    if canRead p then typesOf (factsAt b (S.lookup st p)) else []))

theorem mem_foldl_collect {β : Type} (P : Fact × β → Bool) (g : Fact × β → String)
    (l : List (Fact × β)) (acc : List String) (x : String) :
    x ∈ l.foldl (fun a b => if P b then g b :: a else a) acc ↔
      x ∈ acc ∨ ∃ b ∈ l, P b = true ∧ g b = x := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
      rw [List.foldl_cons, ih]
      by_cases hp : P c = true
      · rw [if_pos hp]
        constructor
        · rintro (hx | ⟨d, hd, hpd, hgd⟩)
          · rcases List.mem_cons.mp hx with hx | hx
            · exact Or.inr ⟨c, List.mem_cons_self .., hp, hx.symm⟩
            · exact Or.inl hx
          · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hpd, hgd⟩
        · rintro (hx | ⟨d, hd, hpd, hgd⟩)
          · exact Or.inl (List.mem_cons_of_mem _ hx)
          · rcases List.mem_cons.mp hd with hd | hd
            · subst hd; exact Or.inl (List.mem_cons.mpr (Or.inl hgd.symm))
            · exact Or.inr ⟨d, hd, hpd, hgd⟩
      · rw [if_neg hp]
        constructor
        · rintro (hx | ⟨d, hd, hpd, hgd⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hpd, hgd⟩
        · rintro (hx | ⟨d, hd, hpd, hgd⟩)
          · exact Or.inl hx
          · rcases List.mem_cons.mp hd with hd | hd
            · subst hd; exact absurd hpd hp
            · exact Or.inr ⟨d, hd, hpd, hgd⟩

/-- **The type index lists exactly the types of the resources the agent may
read.** -/
theorem visibleTypes_eq_specTypes (S : Store σ) (L : StoreLaws S) (st : IxState S)
    (canRead : String → Bool) :
    visibleTypes st.ix canRead = specTypes S st.baseIri canRead st.base := by
  unfold visibleTypes specTypes
  apply orderPaths_ext
  intro t
  rw [TreeMap.foldl_eq_foldl_toList]
  have key := mem_foldl_collect (β := TreeSet String)
    (fun b => b.1.1 == typeRel && b.2.toList.any canRead) (fun b => b.1.2)
    st.ix.byFact.toList [] t
  rw [key]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap]
  constructor
  · rintro ⟨⟨f, ps⟩, hmem, hP, hg⟩
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, TreeSet.mem_toList] at hP
    obtain ⟨hf1, p, hp, hcr⟩ := hP
    have hget := TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
    have hf : f = (typeRel, t) := by cases f; simp_all
    subst hf
    have hpo : p ∈ st.ix.pathsOf (typeRel, t) := by
      unfold IndexData.pathsOf
      rw [TreeMap.getD_eq_getD_getElem?, hget]
      exact hp
    have hfact := (st.ok.mem_iff _ p).mp hpo
    obtain ⟨e, he, _⟩ := some_of_mem_factsAt hfact
    refine ⟨p, ?_, ?_⟩
    · have hc := L.pathsLookup st.base p
      rw [he] at hc
      simpa using hc
    · simp only [hcr, if_true]
      exact (mem_typesOf _ _).mpr hfact
  · rintro ⟨p, _, hp⟩
    split at hp
    · rename_i hcr
      have hfact := (mem_typesOf _ _).mp hp
      have hpo := (st.ok.mem_iff _ p).mpr hfact
      unfold IndexData.pathsOf at hpo
      rw [TreeMap.getD_eq_getD_getElem?] at hpo
      cases hget : st.ix.byFact[(typeRel, t)]? with
      | none => rw [hget] at hpo; simp at hpo
      | some ps =>
          rw [hget] at hpo
          refine ⟨((typeRel, t), ps), TreeMap.mem_toList_iff_getElem?_eq_some.mpr hget, ?_, rfl⟩
          simp only [Option.getD_some] at hpo
          simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, TreeSet.mem_toList, true_and]
          exact ⟨p, hpo, hcr⟩
    · simp at hp

/-! ## Representations -/

/-- The search endpoint and the type index endpoint, absolute. -/
def searchIri (b : String) : String := iriOfPath b typeSearchPath
def indexIri (b : String) : String := iriOfPath b typeIndexPath

/-- The media types of a result: the default first. -/
def resultMedia : List String := [mediaLwsJson, "application/ld+json"]

/-- The media type an `Accept` field admits, or none (406). No field, or an
empty one, gets the default. -/
def chooseResultMedia (accept : Option String) : Option String :=
  match accept with
  | none => some mediaLwsJson
  | some a => if trimS a == "" then some mediaLwsJson else HTTP.negotiate a resultMedia

/-- One result item: `id`, `type` (the native class name, then the other
types), and the container-member metadata of a data resource. -/
def resultItem (b : String) (e : Entry) (facts : List Fact) : Json :=
  let declared := ((typesOf facts).filter (fun t => !nativeClasses.contains t)).eraseDups
  .object (
    [ ("id", .string (iriOfPath b e.path))
    , ("type", .array (.string (if e.kind.isContainer then "Container" else "DataResource") ::
        declared.map Json.string)) ] ++
    (if e.kind.isContainer then []
     else [("format", .string e.contentType), ("size", .number (toString e.body.size))]) ++
    [("modified", .string (isoDateTime e.mtime))])

/-- A ContainerPage of results. It names no container (§QUERY: "the response
does not identify a container"). -/
def searchPageJson (items : List Json) (total : Nat) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile), ("type", .string "ContainerPage")
    , ("totalItems", .number (toString total)), ("items", .array items) ])

/-- A page of the type index. -/
def typeIndexJson (types : List String) (total : Nat) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile), ("type", .string "TypeIndex")
    , ("totalItems", .number (toString total))
    , ("items", .array (types.map (fun t => Json.object [("id", .string t)]))) ])

/-- The pagination links of page `n` of `count`. -/
def pageLinks (target : Nat → String) (n count : Nat) : List Link :=
  [{ target := target 1, rel := "first" }, { target := target count, rel := "last" }] ++
  (if n < count then [{ target := target (n + 1), rel := "next" }] else []) ++
  (if n > 1 then [{ target := target (n - 1), rel := "prev" }] else [])

/-- The header fields of every answer of the two services. -/
def serviceHeaders (b media : String) (links : List Link) : List (String × String) :=
  [ ("content-type", media), ("cache-control", "private"), ("vary", "accept, authorization")
  , ("link", renderLinks (links ++ [{ target := storageIdOf b, rel := lwsStorageRel }])) ]

/-! ## The two services -/

/-- Page `n` (from 1) of the answer `ps` as a ContainerPage, with the page
URIs `link m` in `Link` and `extra` header fields after the service fields. -/
def answerPage (S : Store σ) (cfg : Config) (st : IxState S) (ps : List String) (n : Nat)
    (media method target : String) (link : Nat → String) (extra : List (String × String)) :
    Response :=
  let b := cfg.baseIri
  let count := pageCount ps.length cfg.pageSize
  if n == 0 || n > count then problem 404 "the search has no such page" target
  else
    let page := pageAt ps cfg.pageSize (n - 1)
    let items := page.filterMap (fun p =>
      (S.lookup st.base p).map (fun e => resultItem b e (st.ix.byPath.getD p [])))
    ⟨200, serviceHeaders b media (pageLinks link n count) ++ extra,
     if method == "HEAD" then "" else searchPageJson items ps.length, none⟩

/-- A page of the answer to a filter: `answerPage` of `searchAnswer`, whose
page `n` is `searchPagePaths`. -/
def searchPage (S : Store σ) (cfg : Config) (canRead : String → Bool) (st : IxState S)
    (gs : Filter) (n : Nat) (media method target : String) : Response :=
  let token := filterToken gs
  answerPage S cfg st (searchAnswer st.ix gs canRead) n media method target
    (fun m => searchIri cfg.baseIri ++ "?q=" ++ token ++ "&" ++ pageQuery m)
    [("accept-query", mediaLwsQuery)]

/-- The search reference of a page URI: `q=<token>&page=N`. -/
def searchRef? (query : String) : Option (Filter × Nat) :=
  match query.splitOn "&" with
  | [q, pg] =>
      if q.startsWith "q=" then
        match filterOfToken? (String.ofList (q.toList.drop 2)), pageOfQuery? pg with
        | some gs, some n => some (gs, n)
        | _, _ => none
      else none
  | _ => none

/-- The Type Search Service: QUERY on the endpoint, GET on its page URIs,
OPTIONS. -/
def searchStep (S : Store σ) (cfg : Config) (canRead : String → Bool) (r : Request)
    (query : String) (st : IxState S) : Response :=
  let target := typeSearchPath
  let allow := "OPTIONS, QUERY"
  let aq := ("accept-query", mediaLwsQuery)
  match r.method with
  | "OPTIONS" => ⟨204, [("allow", allow), aq], "", none⟩
  | "QUERY" =>
      match r.header? "content-type" with
      | none => problem 400 "a search names its query format in Content-Type" target [aq]
      | some ct =>
          if baseMedia ct != mediaLwsQuery then
            problem 415 "the search accepts application/lws-query+json" target [aq]
          else match chooseResultMedia (r.header? "accept") with
            | none => problem 406 "the search answers application/lws+json or application/ld+json"
                target [aq, ("vary", "accept, authorization")]
            | some media =>
                match (String.fromUTF8? r.content).map parseJson with
                | none | some (.error _) =>
                    problem 400 "the filter is not well-formed JSON" target [aq]
                | some (.ok j) =>
                    match parseFilter j with
                    | .error (status, msg) => problem status msg target [aq]
                    | .ok gs => searchPage S cfg canRead st gs 1 media "QUERY" target
  | "GET" | "HEAD" =>
      if query == "" then
        problem 405 "the search is a QUERY on this endpoint" target [("allow", allow), aq]
      else match searchRef? query with
        | none => problem 404 "the server does not recognise this page reference" target
        | some (gs, n) =>
            match chooseResultMedia (r.header? "accept") with
            | none => problem 406 "the search answers application/lws+json or application/ld+json"
                target [("vary", "accept, authorization")]
            | some media => searchPage S cfg canRead st gs n media r.method target
  | _ => problem 405 "the search endpoint accepts OPTIONS and QUERY" target [("allow", allow), aq]

/-- The Type Index Service: GET and HEAD of the endpoint and its pages. -/
def typeIndexStep (cfg : Config) (canRead : String → Bool) (r : Request) (query : String)
    {S : Store σ} (st : IxState S) : Response :=
  let target := typeIndexPath
  let allow := "GET, HEAD, OPTIONS"
  match r.method with
  | "OPTIONS" => ⟨204, [("allow", allow)], "", none⟩
  | "GET" | "HEAD" =>
      let pageNo : Option Nat := if query == "" then some 1 else pageOfQuery? query
      match pageNo, chooseResultMedia (r.header? "accept") with
      | none, _ => problem 404 "the type index has no page with this name" target
      | _, none => problem 406 "the type index answers application/lws+json or application/ld+json"
          target [("vary", "accept, authorization")]
      | some n, some media =>
          let ts := visibleTypes st.ix canRead
          let count := pageCount ts.length cfg.pageSize
          if n == 0 || n > count then problem 404 "the type index has no such page" target
          else
            let link (m : Nat) : String := indexIri cfg.baseIri ++ "?" ++ pageQuery m
            ⟨200, serviceHeaders cfg.baseIri media (pageLinks link n count),
             if r.method == "HEAD" then ""
             else typeIndexJson (pageAt ts cfg.pageSize (n - 1)) ts.length, none⟩
  | _ => problem 405 "the type index is read with GET" target [("allow", allow)]

/-- One request to an index service endpoint, as an agent whose read access
is `canRead`. -/
def serviceResponse (S : Store σ) (cfg : Config) (canRead : String → Bool) (r : Request)
    (st : IxState S) : Response :=
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if path == typeIndexPath then typeIndexStep cfg canRead r query st
  else searchStep S cfg canRead r query st

/-- One request to a storage with the index services: authorization
(`Authorization.decide`, which lets any client ask the index services), then
the index service with Web Access Control read access of the requesting agent
over the current state, or the storage, the subscriptions and the
notifications (`Notifications.serverStep`) through the indexed store. -/
def serverStep (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Notifications.Signer) (now : Nat)
    (r : Request) (st : IxState S) (ns : Notifications.NotifState) :
    Sum (String × String) (Response × IxState S × Notifications.NotifState ×
      List Notifications.Delivery) :=
  let IS := IndexedStore S L
  let (path, _) := splitTarget r.path
  if cfg.typeIndex && isIndexServicePath path then
    match Authorization.decide V IS cfg a now r st with
    | .fetch i u => .inl (i, u)
    | .respond resp => .inr (resp, st, ns, [])
    | .proceed agent =>
        .inr (serviceResponse S cfg (Notifications.wacCanRead IS cfg a agent st) r st, st, ns, [])
  else Notifications.serverStep V IS cfg a signer now r st ns

/-- An index service request changes nothing: the state is returned as it
came (§QUERY: "a search never alters server state"). -/
theorem serverStep_index_safe (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S)
    (cfg : Config) (a : Authorization.AuthzConfig) (signer : Option Notifications.Signer)
    (now : Nat) (r : Request) (st : IxState S) (ns : Notifications.NotifState)
    (h : cfg.typeIndex = true ∧ isIndexServicePath (splitTarget r.path).1 = true)
    {resp : Response} {st' : IxState S} {ns' : Notifications.NotifState}
    {ds : List Notifications.Delivery}
    (hr : serverStep V S L cfg a signer now r st ns = .inr (resp, st', ns', ds)) :
    st' = st ∧ ns' = ns ∧ ds = [] := by
  unfold serverStep at hr
  simp only [h.1, h.2, Bool.and_self, if_true] at hr
  split at hr
  · simp at hr
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at hr
    exact ⟨hr.2.1.symm, hr.2.2.1.symm, hr.2.2.2.symm⟩
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at hr
    exact ⟨hr.2.1.symm, hr.2.2.1.symm, hr.2.2.2.symm⟩

end L4Factoidal.LWS.Search
