/-
L4Factoidal.WebAnnotation.Protocol — the Web Annotation Protocol (W3C
Recommendation, 2017-02-23, https://www.w3.org/TR/annotation-protocol/) as
a total request handler over the Linked Web Storage store.

The annotation containers and the annotations are entries of an
`L4Factoidal.LWS.Store`: a container is an LWS container entry, an
annotation is an LWS data resource whose bytes are its JSON-LD text. So
any backend that satisfies `LWS.StoreLaws` (the in-memory `MemStore`, the
`TreeStore`, a storage kept in files) holds annotations, and the listing
order and the pages are the LWS ones (`LWS.orderedMemberPaths`,
`LWS.pageAt`). Theorem `wap2017_page_eq_lws10_page` states this.

The rules, with their sections of the Protocol:

* §3.1, §4.1: GET, HEAD and OPTIONS on annotations and containers; the
  `Link` type header, `ETag`, `Allow`, `Vary`, `Accept-Post`.
* §4: a container path ends in `/`; its IRI has no query.
* §4.2: the container is a `BasicContainer` and an `AnnotationCollection`
  with `total`, `first` and `last`; `Content-Location` equals its `id`;
  `?iris=1` and `?iris=0` tell IRI pages from description pages.
* §4.2.1: the three `Prefer` preferences; no preference means
  PreferContainedDescriptions; PreferMinimalContainer embeds no page.
* §4.3: an `AnnotationPage` has `id`, `partOf`, `startIndex`, `next`
  (unless last) and `prev` (unless first).
* §5.1: POST creates; the server assigns `id` under the container IRI,
  moves an earlier `id` to `via`, keeps `canonical`, uses the `Slug` when
  it is free, answers 201 with `Location`.
* §5.2: PUT replaces; `id` must be the annotation's IRI; a change to a
  `canonical` or `via` that was set is refused; `If-Match` is checked;
  200 with the new state.
* §5.3: DELETE answers 204; the IRI leaves the container and is not used
  again (a later GET answers 410, §6).
* §6: the status codes 400, 404, 405, 410, 412, 415.

Only the JSON-LD representation is served (§3.1: MUST; Turtle is a SHOULD
that this module does not give yet). The handler is pure: the host gives
the request and keeps the state.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.WebAnnotation.Protocol

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-! ## Names -/

def annoContext : String := "http://www.w3.org/ns/anno.jsonld"
def ldpContext : String := "http://www.w3.org/ns/ldp.jsonld"
/-- §3.1: `application/ld+json` with the Web Annotation profile. -/
def mediaType : String := "application/ld+json; profile=\"http://www.w3.org/ns/anno.jsonld\""
def preferMinimal : String := "http://www.w3.org/ns/ldp#PreferMinimalContainer"
def preferIris : String := "http://www.w3.org/ns/oa#PreferContainedIRIs"
def preferDescriptions : String := "http://www.w3.org/ns/oa#PreferContainedDescriptions"

def annotationAllow : String := "GET,HEAD,OPTIONS,PUT,DELETE"
def containerAllow : String := "GET,HEAD,OPTIONS,POST"
def pageAllow : String := "GET,HEAD,OPTIONS"

/-! ## Configuration and state -/

/-- `baseIri` ends with `/` (`LWS.iriOfPath`). `containers` are the paths of
the annotation containers; each ends with `/`. `pageSize` is the number of
annotations on one page; 0 means one page. -/
structure Config where
  baseIri : String := "https://example.org/"
  containers : List String := ["/annotations/"]
  pageSize : Nat := 10
  label : String := "Annotations"
deriving Repr, Inhabited

/-- The store state, and the paths of deleted annotations (§5.3: "The IRIs
of deleted Annotations SHOULD NOT be re-used"; §6: 410). -/
structure State (σ : Type) where
  store : σ
  deleted : List String := []

variable {σ : Type}

/-- A container path is valid when it ends with `/` and has no query or
fragment (§4). -/
def validContainerPath (p : String) : Bool :=
  p.endsWith "/" && !(p.any (fun c => c == '?' || c == '#'))

/-- Create the containers of `cfg` that are missing. -/
def init (S : Store σ) (cfg : Config) (st : σ) : State σ :=
  { store := ensureAncestors S
      (cfg.containers.filter validContainerPath |>.flatMap (fun c => ancestors c ++ [c])) st }

/-! ## JSON helpers -/

def fieldsOf : Json → List (String × Json)
  | .object fs => fs
  | _ => []

def strOf? : Option Json → Option String
  | some (.string s) => some s
  | _ => none

/-- The `type` values of a JSON-LD node: a string or an array of strings. -/
def typeValues (j : Json) : List String :=
  match j.field? "type" with
  | some (.string s) => [s]
  | some (.array xs) => xs.filterMap (fun x => match x with | .string s => some s | _ => none)
  | _ => []

/-- The `@context` values, a string or an array whose strings count. -/
def contextValues (j : Json) : List String :=
  match j.field? "@context" with
  | some (.string s) => [s]
  | some (.array xs) => xs.filterMap (fun x => match x with | .string s => some s | _ => none)
  | _ => []

/-- What a POST or PUT body must be to be taken as an annotation (§5.1, §6
415: "non-Annotation or in a context that is unrecognized"): an object in
the Web Annotation context, of type `Annotation`, with a `target`. The full
Data Model checks are those of `WebAnnotation.JsonTest`; the harness runs
them on every annotation this handler returns. -/
def isAnnotation (j : Json) : Bool :=
  (match j with | .object _ => true | _ => false) &&
  (contextValues j).contains annoContext &&
  (typeValues j).contains "Annotation" &&
  (j.field? "target").isSome

/-- The `via` member that §5.1 adds: the earlier `id` when it differs from
the assigned IRI and `via` is not set. -/
def viaPart (old : Option String) (hasVia : Bool) (iri : String) : List (String × Json) :=
  match old with
  | some o => if o != iri && !hasVia then [("via", .string o)] else []
  | none => []

/-- §5.1: set `id` to the assigned IRI; an earlier `id` that differs is
copied to `via` when `via` is not set. Every other member is kept, in its
order; `canonical` is not touched. -/
def assignId (j : Json) (iri : String) : Json :=
  .object (("id", .string iri) ::
    (viaPart (strOf? (j.field? "id")) (j.field? "via").isSome iri ++
      (fieldsOf j).filter (fun kv => kv.1 != "id")))

/-! ## Requests -/

def isJsonLd (r : Request) : Bool :=
  match r.header? "content-type" with
  | some ct =>
    let t := ((ct.splitOn ";").headD "").trimAscii.toString.toLower
    t == "application/ld+json"
  | none => false

/-- The `include` IRIs of a `Prefer: return=representation` header. -/
def preferIncludes (r : Request) : List String :=
  match r.header? "prefer" with
  | none => []
  | some v =>
    let parts := (v.splitOn ";").map (fun x => x.trimAscii.toString)
    if !(parts.contains "return=representation") then [] else
    parts.flatMap (fun p =>
      if p.startsWith "include=" then
        let raw := (String.ofList (p.toList.drop "include=".length)).trimAscii.toString
        let unq := if raw.startsWith "\"" && raw.endsWith "\"" && raw.length ≥ 2 then
          String.ofList ((raw.toList.drop 1).dropLast) else raw
        (unq.splitOn " ").filter (· != "")
      else [])

/-- How a container answers, from its query and the `Prefer` header. -/
structure View where
  /-- Pages hold IRIs (`?iris=1`) rather than descriptions (`?iris=0`). -/
  iris : Bool
  /-- No page is embedded (§4.2.2). -/
  minimal : Bool
deriving Repr, DecidableEq

/-- §4.2.1. A query `iris=` decides the page kind; otherwise the preference
does, PreferContainedDescriptions by default. -/
def viewOf (r : Request) (q : List (String × String)) : View :=
  let inc := preferIncludes r
  let iris := match q.lookup "iris" with
    | some v => v == "1"
    | none => inc.contains preferIris && !(inc.contains preferDescriptions)
  { iris, minimal := inc.contains preferMinimal }

/-! ## Responses -/

def etagOf (body : String) : String := "\"" ++ hex8 (fnv1a32 body.toUTF8) ++ "\""

def withBody (r : Request) (status : Nat) (hs : List (String × String)) (body : String) :
    Response :=
  { status, headers := hs, body := if r.method == "HEAD" then "" else body }

def plain (status : Nat) (msg : String) (hs : List (String × String) := []) : Response :=
  { status, headers := ("Content-Type", "text/plain; charset=utf-8") :: hs, body := msg ++ "\n" }

def annotationHeaders (body : String) : List (String × String) :=
  [("Content-Type", mediaType),
   ("Link", "<http://www.w3.org/ns/ldp#Resource>; rel=\"type\", <http://www.w3.org/ns/oa#Annotation>; rel=\"type\""),
   ("Allow", annotationAllow), ("Vary", "Accept"), ("ETag", etagOf body)]

def containerLinks : String :=
  "<http://www.w3.org/ns/ldp#BasicContainer>; rel=\"type\", " ++
  "<http://www.w3.org/TR/annotation-protocol/>; rel=\"http://www.w3.org/ns/ldp#constrainedBy\""

/-! ## Container listing -/

/-- The annotation paths of container `c`, in the LWS listing order. -/
def memberPaths (S : Store σ) (st : σ) (c : String) : List String :=
  orderedMemberPaths S st c

/-- The annotations on page `i` (from 0) of container `c`. -/
def pageEntries (S : Store σ) (cfg : Config) (st : σ) (c : String) (i : Nat) : List Entry :=
  (pageAt (memberPaths S st c) cfg.pageSize i).filterMap (S.lookup st)

def pageTotal (cfg : Config) (n : Nat) : Nat := pageCount n cfg.pageSize

def collectionIri (cfg : Config) (c : String) (iris : Bool) : String :=
  iriOfPath cfg.baseIri c ++ "?iris=" ++ (if iris then "1" else "0")

def pageIri (cfg : Config) (c : String) (iris : Bool) (i : Nat) : String :=
  collectionIri cfg c iris ++ "&page=" ++ toString i

def entryJson (e : Entry) : Json := (parseJson? e.text).getD .null

/-- Page `i` (from 0) as JSON-LD (§4.3). `withCtx` is false when the page is
embedded in the container's representation. -/
def pageJson (S : Store σ) (cfg : Config) (st : σ) (c : String) (iris : Bool) (i : Nat)
    (withCtx : Bool) : Json :=
  let ms := memberPaths S st c
  let n := pageTotal cfg ms.length
  let items := (pageEntries S cfg st c i).map (fun e =>
    if iris then Json.string (iriOfPath cfg.baseIri e.path) else entryJson e)
  let ctx : List (String × Json) := if withCtx then [("@context", .string annoContext)] else []
  .object (ctx ++
    [("id", .string (pageIri cfg c iris i)), ("type", .string "AnnotationPage"),
     ("partOf", .object [("id", .string (collectionIri cfg c iris)),
                         ("total", .number (toString ms.length))]),
     ("startIndex", .number (toString (if cfg.pageSize = 0 then 0 else i * cfg.pageSize)))] ++
    (if i + 1 < n then [("next", .string (pageIri cfg c iris (i + 1)))] else []) ++
    (if i > 0 then [("prev", .string (pageIri cfg c iris (i - 1)))] else []) ++
    [("items", .array items)])

/-- The container's representation (§4.2). -/
def containerJson (S : Store σ) (cfg : Config) (st : σ) (c : String) (v : View) : Json :=
  let ms := memberPaths S st c
  let n := pageTotal cfg ms.length
  let first : Json :=
    if v.minimal then .string (pageIri cfg c v.iris 0) else pageJson S cfg st c v.iris 0 false
  .object
    [("@context", .array [.string annoContext, .string ldpContext]),
     ("id", .string (collectionIri cfg c v.iris)),
     ("type", .array [.string "BasicContainer", .string "AnnotationCollection"]),
     ("label", .string cfg.label),
     ("total", .number (toString ms.length)),
     ("first", first),
     ("last", .string (pageIri cfg c v.iris (n - 1)))]

/-! ## The handler -/

/-- What a path names. -/
inductive Target where
  | container (c : String)
  | annotation (c p : String)
  | none

def targetOf (S : Store σ) (cfg : Config) (st : σ) (path : String) : Target :=
  if cfg.containers.contains path && (S.lookup st path).isSome then .container path
  else match parent? path with
    | some c => if cfg.containers.contains c && !path.endsWith "/" then .annotation c path else .none
    | none => .none

/-- The path of a new annotation in `c` (§5.1, Slug): the slug when usable
and free, else `anno` and a number. A path that held a deleted annotation
is not free (§5.3). -/
def newPath (S : Store σ) (s : State σ) (c : String) (slug : Option String) : Option String :=
  let name := match slug with
    | some n => if slugUsable n then n else "anno"
    | none => "anno"
  let taken (n : String) : Bool :=
    (S.lookup s.store (c ++ n)).isSome || (S.lookup s.store (c ++ n ++ "/")).isSome ||
      s.deleted.contains (c ++ n)
  (freeName taken name nameTries 0).map (fun n => c ++ n)

def ifMatchFails (r : Request) (tag : String) : Bool :=
  match r.header? "if-match" with
  | some v => v.trimAscii.toString != "*" && !((v.splitOn ",").map (fun x => x.trimAscii.toString) |>.contains tag)
  | none => false

def storeAnnotation (S : Store σ) (s : State σ) (p : String) (j : Json) : State σ × String :=
  let text := toStringCompact j
  let st := S.tick (S.put s.store
    { path := p, kind := .dataResource, contentType := mediaType,
      body := textBytes text, mtime := S.now s.store })
  ({ s with store := st }, text)

def readQuery (r : Request) : List (String × String) := L4Factoidal.HTTP.parseQuery r.queryStr

/-- One request. -/
def step (S : Store σ) (cfg : Config) (s : State σ) (r : Request) : State σ × Response :=
  let q := readQuery r
  match targetOf S cfg s.store r.path with
  | .container c =>
    let ms := memberPaths S s.store c
    match r.method with
    | "GET" | "HEAD" =>
      match q.lookup "page" with
      | some pg =>
        let iris := (q.lookup "iris") == some "1"
        match pg.toNat? with
        | some i =>
          if i < pageTotal cfg ms.length then
            let body := toStringCompact (pageJson S cfg s.store c iris i true)
            (s, withBody r 200 [("Content-Type", mediaType), ("Allow", pageAllow),
              ("Vary", "Accept, Prefer"), ("ETag", etagOf body)] body)
          else (s, plain 404 "no such page")
        | none => (s, plain 400 "page is not a number")
      | none =>
        let v := viewOf r q
        let body := toStringCompact (containerJson S cfg s.store c v)
        let applied := if (preferIncludes r).isEmpty then [] else
          [("Preference-Applied", "return=representation")]
        (s, withBody r 200 ([("Content-Type", mediaType), ("Link", containerLinks),
          ("Allow", containerAllow), ("Accept-Post", mediaType), ("Vary", "Accept, Prefer"),
          ("ETag", etagOf body), ("Content-Location", collectionIri cfg c v.iris)] ++ applied) body)
    | "OPTIONS" =>
      (s, { status := 200, headers := [("Allow", containerAllow), ("Accept-Post", mediaType),
        ("Link", containerLinks), ("Vary", "Accept, Prefer")] })
    | "POST" =>
      if !isJsonLd r then (s, plain 415 "the body must be application/ld+json") else
      match parseJson? r.body with
      | none => (s, plain 400 "the body is not JSON")
      | some j =>
        if !isAnnotation j then
          (s, plain 415 "the body is not a Web Annotation (context, type Annotation, target)")
        else match newPath S s c (r.header? "slug") with
          | none => (s, plain 409 "no free name")
          | some p =>
            let iri := iriOfPath cfg.baseIri p
            let (s', text) := storeAnnotation S s p (assignId j iri)
            let resp : Response :=
              { status := 201
                body := text
                headers := ("Location", iri) :: annotationHeaders text }
            (s', resp)
    | _ => (s, plain 405 "method not allowed" [("Allow", containerAllow)])
  | .annotation _ p =>
    match S.lookup s.store p with
    | none =>
      if s.deleted.contains p then (s, plain 410 "the annotation was deleted")
      else (s, plain 404 "no such annotation")
    | some e =>
      let text := e.text
      let tag := etagOf text
      let iri := iriOfPath cfg.baseIri p
      match r.method with
      | "GET" | "HEAD" => (s, withBody r 200 (annotationHeaders text) text)
      | "OPTIONS" => (s, { status := 200, headers := [("Allow", annotationAllow), ("Vary", "Accept")] })
      | "PUT" =>
        if ifMatchFails r tag then (s, plain 412 "If-Match does not match") else
        if !isJsonLd r then (s, plain 415 "the body must be application/ld+json") else
        match parseJson? r.body with
        | none => (s, plain 400 "the body is not JSON")
        | some j =>
          if !isAnnotation j then (s, plain 415 "the body is not a Web Annotation") else
          if strOf? (j.field? "id") != some iri then
            (s, plain 400 "the id of the body is not the IRI of the annotation")
          else
            let old := entryJson e
            let changed (k : String) : Bool :=
              (old.field? k).isSome && strOf? (old.field? k) != strOf? (j.field? k)
            if changed "canonical" || changed "via" then
              (s, plain 409 "canonical and via cannot be changed once set")
            else
              let (s', text') := storeAnnotation S s p j
              let resp : Response := { status := 200, body := text', headers := annotationHeaders text' }
              (s', resp)
      | "DELETE" =>
        if ifMatchFails r tag then (s, plain 412 "If-Match does not match") else
        ({ store := S.tick (S.remove s.store p), deleted := p :: s.deleted }, { status := 204 })
      | _ => (s, plain 405 "method not allowed" [("Allow", annotationAllow)])
  | .none => (s, plain 404 "not found")

/-! ## Theorems -/

/-- §5.1: the assigned IRI is the `id`. -/
theorem assignId_id (j : Json) (iri : String) :
    (assignId j iri).field? "id" = some (.string iri) := by
  simp [assignId, Json.field?]

private theorem find_filter_ne (fs : List (String × Json)) (k d : String) (h : k ≠ d) :
    (fs.filter (fun kv => kv.1 != d)).find? (fun kv => kv.1 == k) =
      fs.find? (fun kv => kv.1 == k) := by
  induction fs with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨a1, a2⟩ := a
    by_cases ha : a1 = d
    · subst ha
      simp [ih, Ne.symm h]
    · simp [ha, List.find?_cons, ih]

private theorem viaPart_key {old : Option String} {hv : Bool} {iri : String}
    {kv : String × Json} (h : kv ∈ viaPart old hv iri) : kv.1 = "via" := by
  unfold viaPart at h
  split at h
  · split at h <;> simp_all
  · simp at h

/-- §5.1: "If the Annotation contains a canonical property, then that
reference MUST be maintained without change." -/
theorem assignId_canonical (j : Json) (iri : String) :
    (assignId j iri).field? "canonical" = j.field? "canonical" := by
  cases j with
  | object fs =>
    have hf := find_filter_ne fs "canonical" "id" (by decide)
    simp only [assignId, fieldsOf, Json.field?, List.find?_cons, List.find?_append]
    simp only [hf]
    rw [List.find?_eq_none.mpr (fun kv hm => by simp [viaPart_key hm])]
    simp
  | _ =>
    simp only [assignId, fieldsOf, Json.field?, List.find?_cons, List.find?_append]
    simp
    intro a b hm
    have := viaPart_key hm
    simp_all

/-- §5.1: the path of a new annotation holds nothing, and held no deleted
annotation: a POST never replaces an annotation and never reuses an IRI. -/
theorem newPath_fresh (S : Store σ) (s : State σ) (c : String) (slug : Option String)
    (p : String) (h : newPath S s c slug = some p) :
    S.lookup s.store p = none ∧ p ∉ s.deleted := by
  unfold newPath at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨n, hn, rfl⟩ := h
  have hfree := freeName_free _ _ _ _ _ hn
  simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
    List.contains_eq_mem, decide_eq_false_iff_not] at hfree
  exact ⟨hfree.1.1, hfree.2⟩

/-- §5.1: "The IRI for the Annotation MUST be the IRI of the Container with
an additional component added to the end." -/
theorem newPath_prefix (S : Store σ) (s : State σ) (c : String) (slug : Option String)
    (p : String) (h : newPath S s c slug = some p) : ∃ n, p = c ++ n := by
  unfold newPath at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨n, _, rfl⟩ := h
  exact ⟨n, rfl⟩

/-- Web Annotation Protocol 2017 pages are LWS 1.0 pages: page `i` of a
container holds the entries that the LWS listing gives on its page `i + 1`
(`LWS.pageItems`, pages counted from 1), in the same order. -/
theorem wap2017_page_eq_lws10_page (S : Store σ) (cfg : Config) (st : σ) (c : String) (i : Nat) :
    pageEntries S cfg st c i = pageItems S st c cfg.pageSize (i + 1) := by
  simp [pageEntries, pageItems, memberPaths]

/-- §4.2: "if every page is traversed, a client can reconstruct the
complete, ordered contents of the container/collection." The entries of
pages 0 to `pageTotal - 1` are the container's annotations, each once, in
listing order (from `LWS.pageItems_concat`). -/
theorem wap2017_pages_concat (S : Store σ) (cfg : Config) (st : σ) (c : String) :
    (List.range (pageTotal cfg (memberPaths S st c).length)).flatMap
      (pageEntries S cfg st c) = listedMembers S st c := by
  have h := pageItems_concat S st c cfg.pageSize
  have hn : pageTotal cfg (memberPaths S st c).length = memberPageCount S st c cfg.pageSize := rfl
  rw [hn, show pageEntries S cfg st c = fun i => pageItems S st c cfg.pageSize (i + 1) from
    funext (wap2017_page_eq_lws10_page S cfg st c)]
  exact h

end L4Factoidal.WebAnnotation.Protocol
