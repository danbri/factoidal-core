/-
L4Factoidal.LWS.SearchResults — ANTICIPATORY AND UNSTABLE: a search results
resource that a QUERY answer of the Type Search Service names with
`Content-Location`. https://github.com/danbri/factoidal/issues/922

STATUS. No specification defines this resource. It is off by default
(`Config.searchResults`), it is marked as an extension in the storage
description (`Binding.unstableResultsMember`), and its paths, its lifetime,
its snapshot member and its behaviour are likely to change when lws10-index
says more. Owner, 2026-10-21: "what do we think a Content-Location results
resource looks like? Can we draft an anticipatory impl flagged as likely
unstable?"

Sources, verbatim:

RFC 10008 (The HTTP QUERY Method, June 2026), §2.3 "Content-Location
Response Field": "A successful response (2xx, Section 15.3 of [HTTP]) can
include a Content-Location header field containing an identifier for a
resource corresponding to the results of the operation [...] This represents
a claim from the server that a client can send a GET request for the
indicated URI to retrieve the results of the query operation just performed.
The indicated resource might be temporary."

RFC 10008 §2.4 "Location Response Field": "A server can assign a URI to the
equivalent resource (Section 2.2) of a QUERY request. If the server does so,
the URI of that resource can be included in the Location header field of the
2xx response [...] This represents a claim that a client can send a GET
request to the indicated URI to repeat the query operation just performed
without resending the query content."

RFC 10008 Appendix A.4.1: the Content-Location resource is "a resource
holding the result for the QUERY response it appeared on" and "there is no
guarantee that the server will implement this resource indefinitely, so,
after an error response, the client would need to redo the original QUERY
request". Appendix A.4.2: the Location resource "will respond to GET with a
current result for the same process and parameters".

RFC 10008 §4 (Security Considerations): "If a server creates a temporary
resource to represent the results of a QUERY request (e.g., for use in the
Location or Content-Location field), assigns a URI to that resource, and the
request contains sensitive information that cannot be logged, then that URI
SHOULD be chosen such that it does not include any sensitive portions of the
original request content."

lws10-index §QUERY (w3c/lws-protocol 9a08ff65): "[[!RFC10008]] permits a
response to carry a Content-Location header field identifying a resource that
represents the query results." and "this specification does not define such a
resource; a server that nonetheless exposes one MUST subject it to the same
authorization filtering on every access and MUST prevent its reuse across
clients."

What the RFC text changed in the proposed design of issue 922. The issue
proposed that a GET on the Content-Location resource re-runs the filter
against the current state. RFC 10008 gives that behaviour to the Location
resource (the equivalent resource, "a current result"); the Content-Location
resource holds "the results of the query operation just performed". So this
module keeps the RESULT SET of the QUERY (its paths, `Record.paths`) and
answers a GET with the members of that set that a QUERY with the same filter
by the same agent would still answer now: the filter is evaluated again over
the current state and the agent's current read access is applied again
(`resultsAnswer`). A resource made after the QUERY never appears; a resource
that was deleted, no longer matches, or is no longer readable disappears.
That is the lws10-index MUST ("the same authorization filtering on every
access"), and it never says more than a new QUERY would (theorem
`resultsAnswer_sublist_query`). No Location field is sent: the page URIs of
the search (`?q=<filter>&page=N`, `Search.searchStep`) already repeat the
query by GET.

Server choices, all unstable:
* path `<search endpoint>/results/<id>` (`Binding.searchResultsPath`); `<id>`
  is the base64url form of 16 random bytes the host passes with the request
  (`random`, at least 16 bytes): 128 bits, and nothing of the request content
  (RFC 10008 §4). A request with fewer random bytes gets no results resource.
* only an authenticated QUERY makes one (an anonymous answer names none),
  and it answers only its creating agent with the same client (`client_id`
  of the token, `Authorization.tokenClient?`); any other agent or client and
  an anonymous request get 404, the same answer as for an unknown name
  ("MUST prevent its reuse across clients"; theorem
  `resultsGet_creator_only`).
* lifetime `Config.searchResultsTtl` seconds (default 600), then 410; at
  most `Config.searchResultsMax` records (default 100), the oldest removed
  first (theorem `insertBounded_length_le`), then 404.
* GET, HEAD and OPTIONS; pages `?page=N` at `Config.pageSize`, as the search
  pages; `Cache-Control: private`, `Vary: accept, authorization`.
* snapshot member `searchResults` (`stateJson`, `stateOfJson`), format
  `lws-search-results-unstable-1`, written only when it holds a record.
-/
import L4Factoidal.LWS.Search

namespace L4Factoidal.LWS.SearchResults

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.Search
open L4Factoidal.HTTP (Request Response)

variable {σ : Type}

/-! ## Records -/

/-- One search results resource: the QUERY's filter and result set, who made
it, and when it ends. -/
structure Record where
  id : String
  filter : Filter
  /-- The authenticated agent (token `sub`) of the QUERY. -/
  agent : String
  /-- The `client_id` of the QUERY's token, if it had one. -/
  client : Option String
  created : Nat
  expires : Nat
  /-- The paths the QUERY answered, in its order. -/
  paths : List String
deriving Repr, Inhabited, BEq

/-- The records of a storage, oldest first, and a revision that advances on
every change (so the host knows to persist). -/
structure ResultsState where
  records : List Record := []
  revision : Nat := 0
deriving Repr, Inhabited

/-- The record with this name that the agent and client may read: the
creating agent with the same client, and nobody else. -/
def findFor (rs : ResultsState) (id : String) (agent client : Option String) :
    Option Record :=
  rs.records.find? (fun rc => rc.id == id && agent == some rc.agent && client == rc.client)

/-- **A record answers only its creator.** -/
theorem findFor_creator {rs : ResultsState} {id : String} {agent client : Option String}
    {rc : Record} (h : findFor rs id agent client = some rc) :
    rc ∈ rs.records ∧ rc.id = id ∧ agent = some rc.agent ∧ client = rc.client := by
  unfold findFor at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1.1, hp.1.2, hp.2⟩

/-- No record answers an anonymous request. -/
theorem findFor_anonymous (rs : ResultsState) (id : String) (client : Option String) :
    findFor rs id none client = none := by
  unfold findFor
  apply List.find?_eq_none.mpr
  intro rc _
  simp

/-- Add a record and keep the newest `max`. -/
def insertBounded (max : Nat) (rs : ResultsState) (rc : Record) : ResultsState :=
  let all := rs.records ++ [rc]
  { records := all.drop (all.length - max), revision := rs.revision + 1 }

/-- **The number of records is bounded.** -/
theorem insertBounded_length_le (max : Nat) (rs : ResultsState) (rc : Record) :
    (insertBounded max rs rc).records.length ≤ max := by
  simp only [insertBounded, List.length_drop]
  omega

/-- With room for one, the new record is kept. -/
theorem insertBounded_mem (max : Nat) (rs : ResultsState) (rc : Record) (h : 0 < max) :
    rc ∈ (insertBounded max rs rc).records := by
  simp only [insertBounded]
  have hk : (rs.records ++ [rc]).length - max ≤ rs.records.length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [List.drop_append_of_le_length hk]
  exact List.mem_append_right _ (List.mem_singleton_self rc)

/-- The name of a results resource: the base64url form (RFC 4648 §5) of the
first 16 random bytes the host passed, or none with fewer. -/
def idOfRandom? (rand : Option ByteArray) : Option String :=
  rand.bind fun b => if b.size ≥ 16 then some (JOSE.Base64Url.encode (b.extract 0 16)) else none

/-- Make the record of a QUERY: only for an authenticated agent, with 16
random bytes, a name not in use and room for one record. -/
def create (cfg : Config) (rs : ResultsState) (gs : Filter) (agent client : Option String)
    (now : Nat) (rand : Option ByteArray) (paths : List String) :
    Option Record × ResultsState :=
  match agent, idOfRandom? rand with
  | some a, some id =>
      if cfg.searchResultsMax == 0 || rs.records.any (·.id == id) then (none, rs)
      else
        let rc : Record := { id, filter := gs, agent := a, client, created := now,
                              expires := now + cfg.searchResultsTtl, paths }
        (some rc, insertBounded cfg.searchResultsMax rs rc)
  | _, _ => (none, rs)

/-- **An anonymous QUERY makes no results resource.** -/
theorem create_anonymous (cfg : Config) (rs : ResultsState) (gs : Filter)
    (client : Option String) (now : Nat) (rand : Option ByteArray) (paths : List String) :
    create cfg rs gs none client now rand paths = (none, rs) := by
  simp [create]

/-- A record that `create` makes belongs to the QUERY's agent and client. -/
theorem create_owner {cfg : Config} {rs : ResultsState} {gs : Filter}
    {agent client : Option String} {now : Nat} {rand : Option ByteArray} {paths : List String}
    {rc : Record} {rs' : ResultsState}
    (h : create cfg rs gs agent client now rand paths = (some rc, rs')) :
    agent = some rc.agent ∧ rc.client = client ∧ rc.filter = gs ∧ rc.paths = paths := by
  unfold create at h
  split at h
  · rename_i a id _ _
    split at h
    · simp at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      rw [← h.1]
      exact ⟨rfl, rfl, rfl, rfl⟩
  · simp at h

/-! ## The answer -/

/-- What a GET of a results resource lists: the paths a QUERY with the
record's filter answers now, with the agent's current read access, that were
in the QUERY's result set. -/
def resultsAnswer (ix : IndexData) (rc : Record) (canRead : String → Bool) : List String :=
  (searchAnswer ix rc.filter canRead).filter (fun p => rc.paths.contains p)

/-- **A results resource never says more than a new QUERY.** Its answer is a
sublist of the answer a QUERY with the same filter gets with the same read
access over the same state. -/
theorem resultsAnswer_sublist_query (ix : IndexData) (rc : Record) (canRead : String → Bool) :
    (resultsAnswer ix rc canRead).Sublist (searchAnswer ix rc.filter canRead) :=
  List.filter_sublist

theorem mem_resultsAnswer_query {ix : IndexData} {rc : Record} {canRead : String → Bool}
    {p : String} (h : p ∈ resultsAnswer ix rc canRead) : p ∈ searchAnswer ix rc.filter canRead :=
  (List.mem_filter.mp h).1

/-- Every path of a results resource is one the agent may read now (the same
authorization filtering as the QUERY, `searchAnswer_authorized`). -/
theorem resultsAnswer_authorized {ix : IndexData} {rc : Record} {canRead : String → Bool}
    {p : String} (h : p ∈ resultsAnswer ix rc canRead) : canRead p = true :=
  searchAnswer_authorized (mem_resultsAnswer_query h)

/-- Every path of a results resource was in the QUERY's result set. -/
theorem resultsAnswer_recorded {ix : IndexData} {rc : Record} {canRead : String → Bool}
    {p : String} (h : p ∈ resultsAnswer ix rc canRead) : p ∈ rc.paths := by
  have := (List.mem_filter.mp h).2
  simpa using this

/-- Over an indexed state, the answer is the specified search filtered by
read access and by the result set. -/
theorem resultsAnswer_eq_spec (S : Store σ) (L : StoreLaws S) (st : IxState S) (rc : Record)
    (canRead : String → Bool) :
    resultsAnswer st.ix rc canRead =
      ((specSearch S st.baseIri rc.filter st.base).filter canRead).filter
        (fun p => rc.paths.contains p) := by
  unfold resultsAnswer
  rw [searchAnswer_eq_spec S L st]

/-- Every path on every page of a results resource is in the answer of a new
QUERY. -/
theorem resultsPage_mem_query {ix : IndexData} {rc : Record} {canRead : String → Bool}
    {k i : Nat} {p : String} (h : p ∈ pageAt (resultsAnswer ix rc canRead) k i) :
    p ∈ searchAnswer ix rc.filter canRead :=
  mem_resultsAnswer_query (mem_pageAt h)

/-! ## The resource -/

/-- One request to a results resource, as `agent` with token client `client`
and read access `canRead` over the current state. -/
def resultsGet (S : Store σ) (cfg : Config) (canRead : String → Bool)
    (agent client : Option String) (now : Nat) (rs : ResultsState) (id query : String)
    (r : Request) (st : IxState S) : Response :=
  let target := searchResultsPath id
  let allow := "GET, HEAD, OPTIONS"
  match findFor rs id agent client with
  | none => problem 404 "no search results resource of this name is available to this client" target
  | some rc =>
      if rc.expires ≤ now then
        problem 410 "these search results have expired; send the QUERY again" target
      else match r.method with
        | "OPTIONS" => ⟨204, [("allow", allow)], "", none⟩
        | "GET" | "HEAD" =>
            let pageNo : Option Nat := if query == "" then some 1 else pageOfQuery? query
            match pageNo, chooseResultMedia (r.header? "accept") with
            | none, _ => problem 404 "the search results have no page with this name" target
            | _, none => problem 406
                "the search results are application/lws+json or application/ld+json" target
                [("vary", "accept, authorization")]
            | some n, some media =>
                answerPage S cfg st (resultsAnswer st.ix rc canRead) n media r.method target
                  (fun m => iriOfPath cfg.baseIri target ++ "?" ++ pageQuery m) []
        | _ => problem 405 "a search results resource is read with GET" target [("allow", allow)]

/-- **A results resource answers only its creating agent and client.** Any
answer other than 404 comes from a record made by this agent with this
client. -/
theorem resultsGet_creator_only (S : Store σ) (cfg : Config) (canRead : String → Bool)
    (agent client : Option String) (now : Nat) (rs : ResultsState) (id query : String)
    (r : Request) (st : IxState S)
    (h : (resultsGet S cfg canRead agent client now rs id query r st).status ≠ 404) :
    ∃ rc ∈ rs.records, rc.id = id ∧ agent = some rc.agent ∧ client = rc.client := by
  unfold resultsGet at h
  cases hf : findFor rs id agent client with
  | none => rw [hf] at h; exact absurd rfl h
  | some rc =>
      obtain ⟨hm, hid, ha, hc⟩ := findFor_creator hf
      exact ⟨rc, hm, hid, ha, hc⟩

/-- An anonymous request to a results resource gets 404. -/
theorem resultsGet_anonymous (S : Store σ) (cfg : Config) (canRead : String → Bool)
    (client : Option String) (now : Nat) (rs : ResultsState) (id query : String)
    (r : Request) (st : IxState S) :
    (resultsGet S cfg canRead none client now rs id query r st).status = 404 := by
  unfold resultsGet
  rw [findFor_anonymous]
  rfl

/-! ## The step -/

/-- The filter of a QUERY request, when its content is one. -/
def requestFilter? (r : Request) : Option Filter :=
  match (String.fromUTF8? r.content).map parseJson with
  | some (.ok j) => (parseFilter j).toOption
  | _ => none

/-- What this layer does with one request. -/
inductive Outcome where
  /-- Not a request of this layer: step it as before. -/
  | pass
  /-- Fetch this URL for this issuer first (`Authorization.decide`). -/
  | fetch (issuer url : String)
  /-- The answer, and the records after the request. -/
  | handled (resp : Response) (rs : ResultsState)

/-- One request, when the search results resources are on: a QUERY of the
Type Search Service (answered by `Search.searchStep`, then named with
`Content-Location` when a record is made) or a request to a results
resource. Everything else, and everything when the option is off, passes.
The store is never changed here. -/
def serverStep (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (rand : Option ByteArray) (r : Request)
    (st : IxState S) (rs : ResultsState) : Outcome :=
  let IS := IndexedStore S L
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if !(cfg.typeIndex && cfg.searchResults) then .pass
  else if path == typeSearchPath && r.method == "QUERY" then
    match Authorization.decide V IS cfg a now r st with
    | .fetch i u => .fetch i u
    | .respond resp => .handled resp rs
    | .proceed agent =>
        let canRead := Notifications.wacCanRead IS cfg a agent st
        let resp := searchStep S cfg canRead r query st
        if resp.status != 200 then .handled resp rs
        else match requestFilter? r with
          | none => .handled resp rs
          | some gs =>
              match create cfg rs gs agent (Authorization.tokenClient? r) now rand
                  (searchAnswer st.ix gs canRead) with
              | (none, _) => .handled resp rs
              | (some rc, rs') =>
                  .handled { resp with headers := resp.headers ++
                    [("content-location", iriOfPath cfg.baseIri (searchResultsPath rc.id))] } rs'
  else if isSearchResultsPath path then
    match Authorization.decide V IS cfg a now r st with
    | .fetch i u => .fetch i u
    | .respond resp => .handled resp rs
    | .proceed agent =>
        .handled (resultsGet S cfg (Notifications.wacCanRead IS cfg a agent st) agent
          (Authorization.tokenClient? r) now rs (searchResultsIdOf path) query r st) rs
  else .pass

/-- **Off by default.** With the option off, every request passes to the
storage as before. -/
theorem serverStep_off (V : JOSE.Verifiers) (S : Store σ) (L : StoreLaws S) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (rand : Option ByteArray) (r : Request)
    (st : IxState S) (rs : ResultsState) (h : cfg.searchResults = false) :
    serverStep V S L cfg a now rand r st rs = .pass := by
  simp [serverStep, h]

/-! ## Snapshot -/

/-- The snapshot format of the records (unstable). -/
def formatName : String := "lws-search-results-unstable-1"

def recordJson (rc : Record) : Json :=
  .object [ ("id", .string rc.id), ("filter", filterJson rc.filter)
          , ("agent", .string rc.agent)
          , ("client", match rc.client with | some c => .string c | none => .null)
          , ("created", .number (toString rc.created))
          , ("expires", .number (toString rc.expires))
          , ("paths", .array (rc.paths.map Json.string)) ]

/-- The snapshot member `searchResults`. -/
def stateJson (rs : ResultsState) : Json :=
  .object [ ("format", .string formatName), ("records", .array (rs.records.map recordJson)) ]

private def natField (j : Json) (k : String) : Except String Nat :=
  match j.field? k with
  | some (.number s) => match s.toNat? with
    | some n => .ok n
    | none => .error s!"searchResults: member {k} is not a natural number"
  | _ => .error s!"searchResults: member {k} is required"

def recordOfJson (j : Json) : Except String Record := do
  let id ← match j.getString? "id" with
    | some i => if isSearchResultsPath (searchResultsPath i) then .ok i
                else .error "searchResults: a record name is not base64url"
    | none => .error "searchResults: member id is required"
  let filter ← match j.field? "filter" with
    | some fj => match parseFilter fj with
      | .ok gs => .ok gs
      | .error (_, msg) => .error s!"searchResults: {msg}"
    | none => .error "searchResults: member filter is required"
  let agent ← match j.getString? "agent" with
    | some a => .ok a
    | none => .error "searchResults: member agent is required"
  let client := j.getString? "client"
  let created ← natField j "created"
  let expires ← natField j "expires"
  let paths ← match j.getArray? "paths" with
    | some xs => xs.mapM (fun x => match x with
        | .string p => if validTarget p then .ok p
                       else .error s!"searchResults: {p} is not a storage path"
        | _ => .error "searchResults: a path is not a string")
    | none => .error "searchResults: member paths is required"
  return { id, filter, agent, client, created, expires, paths }

/-- Read the snapshot member again; every record is checked. -/
def stateOfJson (j : Json) : Except String ResultsState := do
  if j.getString? "format" != some formatName then
    throw s!"searchResults: format is not {formatName}"
  let records ← match j.getArray? "records" with
    | some xs => xs.mapM recordOfJson
    | none => .error "searchResults: member records is required"
  return { records }

end L4Factoidal.LWS.SearchResults
