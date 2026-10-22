/-
L4Factoidal.LWS.Notifications — the notifications of the Linked Web
Storage Protocol 1.0 core and the webhook notification suite, decided in
Lean. https://github.com/danbri/factoidal/issues/890

Sources, read 2026-10-21 at w3c/lws-protocol commit
9a08ff65a6670cc5d308ed5e531032f23af30fcc (2026-10-19):

* LWS 1.0 core (https://w3c.github.io/lws-protocol/lws10-core/), section
  "Notifications" (`lws10-core/Notifications.html`) with its subsections
  "Notification Discovery", "Notification Data Model" ("Envelope
  Properties", "Activity Properties", "Activity Types", "Batching
  Notifications") and "Subscriptions" ("Subscription Request",
  "Subscription Scope", "Subscription Authorization", "Subscription
  Response", "Subscription Type Identifiers"); and the "Notifications"
  entries of "Security Considerations" and "Privacy Considerations".
* LWS 1.0 Notification Suite: Webhooks
  (https://w3c.github.io/lws-protocol/lws10-notifications-webhook/,
  `lws10-notifications-webhook/index.html`, "an unofficial proposal"):
  "Creating a Webhook Subscription", "Webhook Authentication" ("Signature
  Requirements", "Signature Verification"), "Subscription Management",
  "Notification Delivery", "Subscription Type Identifier".

## What the core section requires, and what this module does

* Notification Discovery. "A storage MAY support notifications. A storage
  that supports notifications MUST advertise a service object in the
  service array of its storage description resource with type equal to
  NotificationService." with a `serviceEndpoint` and a `subscriptionType`
  array. `Binding.storageDescription` (with `Config.notifications`).
* Notification Data Model. The envelope: `type` "MUST be the string
  Notification", `storage`, `activity` (an object or an array). Each
  activity "MUST include" `id`, `type` (an array with at least one
  Activity Streams 2.0 activity type), `object` (with `id` and a `type`
  array: `Container` or `DataResource`) and `published` (RFC 3339);
  OPTIONAL `actor`, `target` ("Used with Create and Move"), `origin`
  ("Used with Delete and Move"). `activityJson`, `envelopeJson`.
* Activity Types. "A server MUST support the following Activity Streams
  2.0 activity types": Create (with `target`), Update, Delete (with
  `origin`). `classify` derives the type from the store before and after
  the step. "A server that allows clients to move resources between
  containers, as described in Moving Resources, MUST support the following
  activity type: Move — a resource was moved from one container to
  another. The origin field indicates the container from which the resource
  was removed, and the target field indicates the container into which it
  was added. The object field describes the resource as it exists after
  the move." and, from §Moving Resources, "A server that advertises support
  for moving resources and emits notifications SHOULD describe a successful
  move with a single Move activity [...] rather than with a separate Delete
  and Create activity." `moveChange?` (https://github.com/danbri/factoidal/issues/914):
  a move (`L4Factoidal.LWS.Move`) gives ONE Move activity about the moved
  resource at its new identifier; the descendants of a moved container
  give none. A subscription hears it when its scope holds the old or the
  new identifier, and its agent may read the resource after the move.
* Batching. "A server MAY combine multiple activities into a single
  notification envelope": one envelope per subscription per request, with
  an array when one request changed more than one resource in its scope.
* Subscriptions. "an authenticated POST request to the serviceEndpoint
  [...] The request body MUST conform to the application/lws+json media
  type"; `type` (one of the advertised types) and `topic` (an array of
  URIs) are REQUIRED. `subscribe`.
* Subscription Scope. "A subscription to a container is recursive [...] A
  subscription to a data resource applies only to that individual
  resource." `inScope`.
* Subscription Authorization. "If a subscriber does not have the
  equivalent of read access to all resources listed in the topic array,
  the server MUST reject the subscription request." (403) and "A server
  MUST NOT deliver a notification about a resource that the subscriber is
  not authorized to read at the time the event occurs." `eligible`,
  theorem `routed_authorized`. The access check is a PARAMETER
  (`canRead`); `serverStep` instantiates it with Web Access Control over
  the storage's ACL resources (`Authorization`). "at the time the event
  occurs" is the store after the step for Create and Update, and the store
  before it for Delete (after the step the resource and its ACL are gone).
  A subscription whose agent lost access to some topics stays; only the
  affected deliveries stop ("The server SHOULD NOT terminate the entire
  subscription").
* Subscription Response. `type` and `subscription` (a URL), in
  `application/lws+json`. 201 with `Location`.
* Privacy: "The actor property SHOULD be omitted by default." It is always
  omitted.

## The webhook suite

* "the subscription body MUST include a type field equal to
  WebhookSubscription", `inbox` REQUIRED, `expires` OPTIONAL; the response
  carries `expires` when the request did. An `expires` that is not an RFC
  3339 date-time, or that is not in the future, is refused with 400.
* Subscription Management: the `serviceEndpoint` lists "a subscriber's
  active webhook subscriptions" as an LWS container (paged at
  `Config.pageSize`, the core's "LWS Paging"); each subscription supports
  GET and DELETE. A subscriber sees only its own subscriptions; another
  agent's subscription answers 404.
* Notification Delivery: an HTTP POST of the envelope to the `inbox`, the
  body `application/lws+json`. "Retry: On failure, the server MAY retry
  delivery." and "Expiration: After repeated failures, the server MAY
  deactivate the subscription." `deliveryResult`: up to `maxAttempts`
  attempts for a status that may pass on a later try (no answer, 408,
  425, 429, 5xx); 410 Gone deactivates at once; `failureLimit` failed
  deliveries in a row deactivate.
* Webhook Authentication: "A server SHOULD sign each outbound request
  using HTTP Message Signatures [RFC9421]", covering `@method`, `@scheme`,
  `@authority`, `@path`, `content-type` and `content-digest` (RFC 9530),
  with `created` and `keyid`; the key is published in the storage
  description as a `JsonWebKey` verification method referenced from
  `authentication`. `signedHeaders` with an Ed25519 `Signer` (the HACL*
  code, `L4Factoidal.Crypto.Ed25519`, supplied by the wasm layer).

## What the host does

Only I/O. `serverStep` returns the deliveries to make (URL, header fields,
body); the host POSTs them, reports each answer's status to
`deliveryResult`, and waits the number of seconds that function names
before a retry. Which resources changed, which subscribers hear of it,
what the body says, how it is signed, whether to retry and when a
subscription is deactivated are all decided here.

## Server choices the drafts leave open, each stated once

* The endpoint is `subscriptionsPath`; a subscription is a member below
  it.
* A topic must be an IRI inside this storage; another IRI is refused
  with 400.
* Auxiliary resources (ACL, metadata) give no activity: the activity types
  name "Storage Resource changes", and the object types are `Container` and
  `DataResource`. A linkset change is an Update of its resource ("content
  or metadata was modified").
* The inbox must be an `http` or `https` URL, and not a container of this
  storage (a delivery POSTed there would create a resource, whose Create
  would be delivered again), and not this server under another host name, IP
  address or `localhost` (`InboxGuard.loops`, 400;
  https://github.com/danbri/factoidal/issues/915). For an inbox host that is
  a name, the engine asks the host to resolve it first (`resolveNeeded?`, the
  `resolve` answer of the wasm ABI).
* The webhook suite, "Security Considerations": "Subscription Abuse: Rate
  limiting and endpoint verification are suggested to prevent abuse of the
  subscription mechanism." Rate limiting (issue 915): at most
  `Config.deliveryLimit` deliveries (default 10) per subscription in a window
  of `Config.deliveryWindow` seconds (default 60); 0 turns it off
  (`admit`, theorems `admits_le`, `admit_count_le`). The activities of a
  change over the limit wait (`NotifState.held`, at most `heldLimit` in all,
  the oldest dropped first) and go, when the window ends, in ONE envelope
  with an `activity` array (core §Batching Notifications: "A server MAY
  combine multiple activities into a single notification envelope by
  providing an array of activity objects as the value of the activity
  property"): at the subscription's next change, or when the host calls
  `lwsFlush` after the seconds the engine named (`nextWake`, `flush`).
  Endpoint verification: the drafts describe no procedure for it (no
  verification request, no challenge, no expected answer), so this server
  makes none.
-/
import L4Factoidal.LWS.Authorization
import L4Factoidal.LWS.Snapshot
import L4Factoidal.LWS.InboxGuard
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.LWS.Notifications

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-! ## RFC 3339 date-times (the `expires` member) -/

private def digits? (cs : List Char) : Option Nat :=
  if !cs.isEmpty && cs.all Char.isDigit then (String.ofList cs).toNat? else none

def leapYear (y : Nat) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 2 => if leapYear y then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-- Days since 1970-01-01 of a civil date in or after 1970: the inverse of
`Binding.civilOfDays` (Howard Hinnant's era algorithm). -/
def daysFromCivil (y m d : Nat) : Nat :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- An RFC 3339 §5.6 `date-time` to seconds since the Unix epoch. A
fraction of a second is dropped and a leap second counts as second 59.
`none` for anything else, and for a time before 1970. -/
def parseRfc3339? (s : String) : Option Nat := do
  let cs := s.toList
  let num (a b : Nat) : Option Nat := digits? ((cs.drop a).take (b - a))
  let at? (i : Nat) (c : Char) : Bool := cs[i]? == some c
  if !(at? 4 '-' && at? 7 '-' && (at? 10 'T' || at? 10 't') && at? 13 ':' && at? 16 ':') then
    none
  let y ← num 0 4
  let mo ← num 5 7
  let d ← num 8 10
  let h ← num 11 13
  let mi ← num 14 16
  let se ← num 17 19
  let rest := cs.drop 19
  let rest := match rest with
    | '.' :: r =>
        let ds := r.takeWhile Char.isDigit
        if ds.isEmpty then ['!'] else r.drop ds.length
    | r => r
  let off : Int ← match rest with
    | ['Z'] | ['z'] => some 0
    | [sg, h1, h2, ':', m1, m2] =>
        if sg == '+' || sg == '-' then do
          let oh ← digits? [h1, h2]
          let om ← digits? [m1, m2]
          if oh < 24 && om < 60 then
            some (if sg == '+' then ((oh * 3600 + om * 60 : Nat) : Int)
                  else -((oh * 3600 + om * 60 : Nat) : Int))
          else none
        else none
    | _ => none
  if !(1970 ≤ y && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ daysInMonth y mo &&
       h < 24 && mi < 60 && se ≤ 60) then none
  let localSecs : Nat := daysFromCivil y mo d * 86400 + h * 3600 + mi * 60 + min se 59
  let utc : Int := (localSecs : Int) - off
  if utc < 0 then none else some utc.toNat

/-! ## Changes: what a step did to the store -/

/-- The activity types LWS §Activity Types requires: Create, Update,
Delete, and Move for a server that moves resources. A Move carries the
path the resource was moved from. -/
inductive ChangeType where
  | create
  | update
  | delete
  | move (origin : String)
deriving DecidableEq, Repr, Inhabited

/-- The Activity Streams 2.0 activity type name. -/
def ChangeType.name : ChangeType → String
  | .create => "Create"
  | .update => "Update"
  | .delete => "Delete"
  | .move _ => "Move"

/-- One change to one resource. -/
structure Change where
  type : ChangeType
  path : String
  kind : ResourceKind
deriving DecidableEq, Repr, Inhabited

/-- Did a stored resource change between two versions: its modification
time, its client links, its media type or its bytes? The time alone is not
enough: a host with a real clock sets the store's clock from the request,
so two writes within one second carry the same time (measured 2026-10-21:
`tests/lws/authorization.mjs` lost an Update this way). A linkset write
changes the client links and keeps the time. -/
def entryChanged (a b : Entry) : Bool :=
  a.mtime != b.mtime || a.links != b.links || a.contentType != b.contentType ||
    a.body.data != b.body.data

variable {σ : Type}

/-- The change at one path, decided from the store before (`pre`) and
after (`post`) a step: Create when the path did not resolve and now does,
Delete when it did and now does not, Update when it resolves in both and
the entry changed. Auxiliary resources give no change. -/
def classify (S : Store σ) (pre post : σ) (p : String) : Option Change :=
  match S.lookup pre p, S.lookup post p with
  | none, none => none
  | none, some e => if e.kind.isAuxiliary then none else some ⟨.create, p, e.kind⟩
  | some e, none => if e.kind.isAuxiliary then none else some ⟨.delete, p, e.kind⟩
  | some a, some b =>
      if !b.kind.isAuxiliary && entryChanged a b then some ⟨.update, p, b.kind⟩ else none

/-- Was the response a success (2xx)? -/
def isSuccess (resp : Response) : Bool := 200 ≤ resp.status && resp.status < 300

/-- The paths a request may have changed, named by its method and its
response; `classify` decides which of them did change and how. A PUT can
create its missing ancestor containers (Solid Protocol §5.3), a POST
creates the path its `Location` names, and a DELETE with `Depth: infinity`
removes the descendants of a container. -/
def candidatePaths (S : Store σ) (r : Request) (resp : Response) (pre : σ) : List String :=
  let (path, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  if !isSuccess resp || !validTarget path then []
  else if query == linksetQuery then [path]
  else if path == storagePath then []
  else match r.method with
    | "PUT" => (ancestors path).filter (fun a => (S.lookup pre a).isNone) ++ [path]
    | "PATCH" => [path]
    | "POST" =>
        match resp.headers.lookup "location" with
        | some l => [l]
        | none => []
    | "DELETE" =>
        (if pathIsContainer path then
           (S.paths pre).filter (fun p => p != path && p.startsWith path)
         else []) ++ [path]
    | _ => []

/-- Is the request a successful one on a linkset resource? -/
def moveCandidate (r : Request) (resp : Response) : Bool :=
  let (_, query0) := splitTarget r.path
  let query := if r.queryStr != "" then r.queryStr else query0
  isSuccess resp && query == linksetQuery

/-- A Move from `path` to `q` when the stores before and after say so. -/
def moveAt (S : Store σ) (pre post : σ) (path q : String) : Option Change :=
  match S.lookup pre path, S.lookup post path, S.lookup pre q, S.lookup post q with
  | some _, none, none, some e =>
      if e.kind.isAuxiliary then none else some ⟨.move path, q, e.kind⟩
  | _, _, _, _ => none

/-- The Move of a step, when it moved a resource (LWS §Moving Resources):
a successful request on a linkset resource whose response names the new
linkset with `Content-Location` (`Operations.linksetStep`), where the old
path resolved before the step and not after it, and the new path did not
resolve before and does after. -/
def moveChange? (S : Store σ) (r : Request) (resp : Response) (pre post : σ) : Option Change :=
  if !moveCandidate r resp then none else
  (resp.headers.lookup "content-location").bind (fun cl =>
    moveAt S pre post (splitTarget r.path).1 (splitTarget cl).1)

/-- The changes one step made, in the order the request made them. A move
is one Move. -/
def changesOf (S : Store σ) (r : Request) (resp : Response) (pre post : σ) : List Change :=
  match moveChange? S r resp pre post with
  | some c => [c]
  | none => (candidatePaths S r resp pre).filterMap (classify S pre post)

/-- A Move names a path that resolved before the step and not after it,
and a new path that did not resolve before the step and does after it. -/
theorem moveChange_sound {S : Store σ} {r : Request} {resp : Response} {pre post : σ}
    {c : Change} (h : moveChange? S r resp pre post = some c) :
    c.kind.isAuxiliary = false ∧ ∃ o, c.type = .move o ∧
      (S.lookup pre o).isSome ∧ S.lookup post o = none ∧
      S.lookup pre c.path = none ∧ (S.lookup post c.path).isSome := by
  unfold moveChange? at h
  split at h
  · simp at h
  obtain ⟨cl, _, hc⟩ := Option.bind_eq_some_iff.mp h
  unfold moveAt at hc
  cases h1 : S.lookup pre (splitTarget r.path).1 <;> cases h2 : S.lookup post (splitTarget r.path).1 <;>
    cases h3 : S.lookup pre (splitTarget cl).1 <;> cases h4 : S.lookup post (splitTarget cl).1 <;>
    simp only [h1, h2, h3, h4] at hc <;> try (simp at hc; done)
  rename_i a e
  split at hc
  · simp at hc
  · rename_i hk
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨by simpa using hk, _, rfl, by simp [h1], h2, h3, by simp [h4]⟩

/-- `classify` gives Create, Delete or Update, never Move. -/
theorem classify_type {S : Store σ} {pre post : σ} {p : String} {c : Change}
    (h : classify S pre post p = some c) :
    c.type = .create ∨ c.type = .delete ∨ c.type = .update := by
  unfold classify at h
  split at h
  · simp at h
  all_goals (split at h <;> simp at h <;> subst h <;> simp)

/-- **The activity type agrees with the store.** A Create names a path that
did not resolve before the step and resolves after it; a Delete one that
resolved before and does not after; an Update one that resolves in both.
No change names an auxiliary resource. -/
theorem classify_sound {S : Store σ} {pre post : σ} {p : String} {c : Change}
    (h : classify S pre post p = some c) :
    c.path = p ∧ c.kind.isAuxiliary = false ∧
    (c.type = .create → S.lookup pre p = none ∧ (S.lookup post p).isSome) ∧
    (c.type = .delete → (S.lookup pre p).isSome ∧ S.lookup post p = none) ∧
    (c.type = .update → (S.lookup pre p).isSome ∧ (S.lookup post p).isSome) := by
  unfold classify at h
  split at h
  · simp at h
  · rename_i e h1 h2
    split at h
    · simp at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp_all
  · rename_i e h1 h2
    split at h
    · simp at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp_all
  · rename_i a b h1 h2
    split at h
    · rename_i hk
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
      simp_all
    · simp at h

/-- Every change `changesOf` reports satisfies `classify_sound` at its own
path. -/
theorem mem_changesOf_sound {S : Store σ} {r : Request} {resp : Response} {pre post : σ}
    {c : Change} (h : c ∈ changesOf S r resp pre post) :
    c.kind.isAuxiliary = false ∧
    (c.type = .create → S.lookup pre c.path = none ∧ (S.lookup post c.path).isSome) ∧
    (c.type = .delete → (S.lookup pre c.path).isSome ∧ S.lookup post c.path = none) ∧
    (c.type = .update → (S.lookup pre c.path).isSome ∧ (S.lookup post c.path).isSome) ∧
    (∀ o, c.type = .move o → (S.lookup pre o).isSome ∧ S.lookup post o = none ∧
      S.lookup pre c.path = none ∧ (S.lookup post c.path).isSome) := by
  unfold changesOf at h
  split at h
  · rename_i c' hm
    simp only [List.mem_singleton] at h
    subst h
    obtain ⟨hk, o, ho, h1, h2, h3, h4⟩ := moveChange_sound hm
    refine ⟨hk, fun hc => ?_, fun hc => ?_, fun hc => ?_, fun o' ho' => ?_⟩
    · rw [ho] at hc; cases hc
    · rw [ho] at hc; cases hc
    · rw [ho] at hc; cases hc
    · rw [ho] at ho'; cases ho'; exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp h
    have hs := classify_sound hp
    rw [hs.1]
    refine ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
    intro o ho
    rcases classify_type hp with h | h | h <;> rw [h] at ho <;> cases ho

/-- A failed request changes nothing that is reported. -/
theorem changesOf_failure {S : Store σ} {r : Request} {resp : Response} {pre post : σ}
    (h : isSuccess resp = false) : changesOf S r resp pre post = [] := by
  simp [changesOf, moveChange?, moveCandidate, candidatePaths, h]

/-- A PATCH or a POST reports at most one change. -/
theorem changesOf_single {S : Store σ} {r : Request} {resp : Response} {pre post : σ}
    (h : r.method = "PATCH" ∨ r.method = "POST") :
    (changesOf S r resp pre post).length ≤ 1 := by
  have hc : (candidatePaths S r resp pre).length ≤ 1 := by
    unfold candidatePaths
    rcases h with h | h
    all_goals
      simp only [h]
      repeat' split
      all_goals simp
  unfold changesOf
  split
  · simp
  · exact Nat.le_trans (List.length_filterMap_le _ _) hc

/-! ## Activities and envelopes (LWS §Notification Data Model) -/

def asContext : String := "https://www.w3.org/ns/activitystreams"

/-- The object type of a resource: `Container` or `DataResource`. -/
def objectType (k : ResourceKind) : String :=
  if k.isContainer then "Container" else "DataResource"

private def hexByte (b : UInt8) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- An RFC 9562 version 8 UUID from the first 16 bytes of a digest. -/
def uuidOfDigest (h : ByteArray) : String :=
  let bs := (h.data.toList ++ List.replicate 16 (0 : UInt8)).take 16
  let bs := bs.zipIdx.map (fun (b, i) =>
    if i == 6 then (b &&& 0x0f) ||| 0x80
    else if i == 8 then (b &&& 0x3f) ||| 0x80
    else b)
  let hx := String.join (bs.map hexByte)
  let part (a n : Nat) : String := String.ofList ((hx.toList.drop a).take n)
  part 0 8 ++ "-" ++ part 8 4 ++ "-" ++ part 12 4 ++ "-" ++ part 16 4 ++ "-" ++ part 20 12

/-- The identifier of the `n`-th activity of a server run. `run` is a tag
derived from the host's entropy at open time, so two runs of one storage
give different identifiers: "A string uniquely identifying the activity". -/
def activityId (run : String) (n : Nat) : String :=
  "urn:uuid:" ++ uuidOfDigest (L4Factoidal.Crypto.sha256 ("lws-activity:" ++ run ++ ":" ++ toString n).toUTF8)

/-- One activity (LWS §Activity Properties). No `actor`: "The actor
property SHOULD be omitted by default." -/
def activityJson (baseIri id published : String) (c : Change) : Json :=
  .object (
    [ ("id", .string id)
    , ("type", .array [.string c.type.name])
    , ("object", .object [ ("id", .string (iriOfPath baseIri c.path))
                         , ("type", .array [.string (objectType c.kind)]) ]) ] ++
    (match c.type, parent? c.path with
     | .create, some p => [("target", .string (iriOfPath baseIri p))]
     | .delete, some p => [("origin", .string (iriOfPath baseIri p))]
     | .move o, some p =>
         (match parent? o with
          | some q => [("origin", .string (iriOfPath baseIri q))]
          | none => []) ++ [("target", .string (iriOfPath baseIri p))]
     | _, _ => []) ++
    [ ("published", .string published) ])

/-- The notification envelope (LWS §Envelope Properties). One activity is
an object; several are an array (§Batching Notifications). -/
def envelopeJson (baseIri : String) (acts : List Json) : Json :=
  .object
    [ ("@context", .array [.string lwsProfile, .string asContext])
    , ("type", .string "Notification")
    , ("storage", .string (storageIdOf baseIri))
    , ("activity", match acts with
        | [a] => a
        | _ => .array acts) ]

/-! ## Subscriptions -/

/-- One subscription. `owner` is the agent that made it (the token's
`sub`), or `none` in the development mode with no agent. -/
structure Subscription where
  id : String
  owner : Option String
  topics : List String
  inbox : String
  expires : Option String := none
  expiresAt : Option Nat := none
  created : Nat
  failures : Nat := 0
  active : Bool := true
  /-- The delivery window (`admit`): when it began and how many deliveries
  went in it. Not persisted. -/
  windowStart : Nat := 0
  windowCount : Nat := 0
deriving Repr, Inhabited, DecidableEq

/-- Is the subscription delivering at time `now`? -/
def live (now : Nat) (s : Subscription) : Bool :=
  s.active && (match s.expiresAt with
    | some t => decide (now < t)
    | none => true)

/-- LWS §Subscription Scope: a container topic covers itself and every
resource transitively contained in it; a data resource topic covers only
itself. -/
def inScope (s : Subscription) (p : String) : Bool :=
  s.topics.any (fun t => t == p || (pathIsContainer t && p.startsWith t))

/-- A delivery not yet acknowledged by its inbox. -/
structure Pending where
  id : String
  subId : String
  inbox : String
  body : String
  attempt : Nat
deriving Repr, Inhabited, DecidableEq

/-- The notification state of one storage. `seq` numbers subscriptions,
activities and deliveries; `revision` advances when a subscription is
made, cancelled or deactivated, so the host knows to persist. -/
structure NotifState where
  subs : List Subscription := []
  seq : Nat := 0
  revision : Nat := 0
  pending : List Pending := []
  /-- The run tag of `activityId`. -/
  run : String := ""
  /-- Activities over the delivery limit, waiting for the end of their
  subscription's window: (subscription id, activity), oldest first. -/
  held : List (String × Json) := []
deriving Repr, Inhabited

/-- The most deliveries kept waiting for an answer; the oldest are dropped. -/
def pendingLimit : Nat := 256

/-- Attempts per delivery before it counts as failed. -/
def maxAttempts : Nat := 3

/-- Failed deliveries in a row that deactivate a subscription. -/
def failureLimit : Nat := 3

/-- The most activities kept waiting over the delivery limit, in all; the
oldest are dropped first. -/
def heldLimit : Nat := 1024

/-- The delivery rate: at most `limit` deliveries per subscription in a
window of `window` seconds; `limit` 0 turns the limit off. -/
structure Rate where
  limit : Nat := 10
  window : Nat := 60
deriving Repr, Inhabited

/-- The rate of a configuration. -/
def _root_.L4Factoidal.LWS.Config.rate (cfg : Config) : Rate := ⟨cfg.deliveryLimit, cfg.deliveryWindow⟩

/-- **One delivery decision** for subscription `s` at time `now`: a window
that has ended starts again at `now`; then a delivery is admitted when the
window has had fewer than `limit` deliveries, and counted. -/
def admit (rate : Rate) (now : Nat) (s : Subscription) : Bool × Subscription :=
  let s0 := if s.windowStart + rate.window ≤ now then { s with windowStart := now, windowCount := 0 } else s
  if rate.limit == 0 then (true, s0)
  else if s0.windowCount < rate.limit then (true, { s0 with windowCount := s0.windowCount + 1 })
  else (false, s0)

/-- The number of deliveries `admit` lets through for decisions at the times
`ts`, in order. -/
def admits (rate : Rate) : List Nat → Subscription → Nat
  | [], _ => 0
  | t :: ts, s => (if (admit rate t s).1 then 1 else 0) + admits rate ts (admit rate t s).2

/-- **At most `limit` deliveries in one window.** For decisions at times
before the end of the subscription's window, `admit` lets through at most
the number of deliveries left in that window. -/
theorem admits_le (rate : Rate) (hl : 0 < rate.limit) :
    ∀ (ts : List Nat) (s : Subscription), (∀ t ∈ ts, t < s.windowStart + rate.window) →
      s.windowCount ≤ rate.limit → admits rate ts s ≤ rate.limit - s.windowCount := by
  intro ts
  induction ts with
  | nil => intro s _ _; simp [admits]
  | cons t ts ih =>
      intro s hts hc
      have ht : ¬ (s.windowStart + rate.window ≤ t) := by
        have := hts t (List.mem_cons_self ..); omega
      have hl0 : (rate.limit == 0) = false := by
        cases h : rate.limit with
        | zero => omega
        | succ _ => rfl
      have hrest : ∀ x ∈ ts, x < s.windowStart + rate.window :=
        fun x hx => hts x (List.mem_cons_of_mem _ hx)
      by_cases hlt : s.windowCount < rate.limit
      · have hadm : admit rate t s = (true, { s with windowCount := s.windowCount + 1 }) := by
          simp [admit, ht, hl0, hlt]
        simp only [admits, hadm, ↓reduceIte]
        have := ih { s with windowCount := s.windowCount + 1 } hrest (by simp; omega)
        simp only at this
        omega
      · have hadm : admit rate t s = (false, s) := by
          simp [admit, ht, hl0, hlt]
        simp only [admits, hadm, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih s hrest hc

/-- A decision keeps the count of its window within the limit. -/
theorem admit_count_le (rate : Rate) (now : Nat) (s : Subscription) (hl : 0 < rate.limit)
    (hc : s.windowCount ≤ rate.limit) : (admit rate now s).2.windowCount ≤ rate.limit := by
  have hl0 : (rate.limit == 0) = false := by
    cases h : rate.limit with
    | zero => omega
    | succ _ => rfl
  unfold admit
  by_cases hw : s.windowStart + rate.window ≤ now
  · simp only [hw, ↓reduceIte, hl0, Bool.false_eq_true]
    split <;> simp_all <;> omega
  · simp only [hw, ↓reduceIte, hl0, Bool.false_eq_true]
    split <;> simp_all <;> omega

/-- What signs deliveries: the verification method identifier and the
signing function (Ed25519 in the wasm layer). -/
structure Signer where
  keyId : String
  sign : ByteArray → ByteArray

/-! ## Delivery requests (webhook suite §Notification Delivery, §Webhook Authentication) -/

/-- The scheme, the authority and the path of an `http` or `https` URL, as
RFC 9421 §2.2 derives `@scheme`, `@authority` (lower case, default port
removed) and `@path` (`/` when empty). `none` for any other URL, or one
with user information, white space or a control character. -/
def urlParts? (u : String) : Option (String × String × String) :=
  if u.length > 2048 || u.any (fun (c : Char) => decide (c.toNat ≤ 32) || c.toNat == 127) then none else
  match u.splitOn "://" with
  | [scheme, rest] =>
      let sch := scheme.toLower
      if sch != "http" && sch != "https" then none else
      let authCs := rest.toList.takeWhile (fun (c : Char) => c != '/' && c != '?' && c != '#')
      let after := rest.toList.drop authCs.length
      let pathCs := (after.takeWhile (fun (c : Char) => c != '#')).takeWhile (fun (c : Char) => c != '?')
      let auth := (String.ofList authCs).toLower
      if auth == "" || authCs.contains '@' then none else
      let auth :=
        if sch == "http" && auth.endsWith ":80" then (auth.dropEnd 3).toString
        else if sch == "https" && auth.endsWith ":443" then (auth.dropEnd 4).toString
        else auth
      some (sch, auth, if pathCs.isEmpty then "/" else String.ofList pathCs)
  | _ => none

/-- RFC 9530 `Content-Digest` with SHA-256, a Structured Field byte
sequence (RFC 8941 §3.3.5: base64 between colons). -/
def contentDigest (body : String) : String :=
  "sha-256=:" ++ Base64.encode (L4Factoidal.Crypto.sha256 body.toUTF8) ++ ":"

/-- The covered components, in order (webhook suite §Signature
Requirements). -/
def coveredComponents : List String :=
  ["@method", "@scheme", "@authority", "@path", "content-type", "content-digest"]

/-- The `@signature-params` value (RFC 9421 §2.3). -/
def signatureParams (created : Nat) (keyId : String) : String :=
  "(" ++ " ".intercalate (coveredComponents.map (fun c => "\"" ++ c ++ "\"")) ++ ")" ++
  ";created=" ++ toString created ++ ";keyid=\"" ++ keyId ++ "\";alg=\"ed25519\""

/-- The signature base (RFC 9421 §2.5) of a delivery POST. -/
def signatureBase (scheme authority path digest params : String) : String :=
  "\"@method\": POST\n" ++
  "\"@scheme\": " ++ scheme ++ "\n" ++
  "\"@authority\": " ++ authority ++ "\n" ++
  "\"@path\": " ++ path ++ "\n" ++
  "\"content-type\": " ++ mediaLwsJson ++ "\n" ++
  "\"content-digest\": " ++ digest ++ "\n" ++
  "\"@signature-params\": " ++ params

/-- One delivery request for the host to make: a POST of `body` to `url`
with exactly these header fields. -/
structure Delivery where
  id : String
  url : String
  headers : List (String × String)
  body : String
deriving Repr, Inhabited, DecidableEq

/-- The request of one attempt of a pending delivery, signed at `now` when
there is a signer. -/
def deliveryOf (signer : Option Signer) (now : Nat) (p : Pending) : Delivery :=
  let digest := contentDigest p.body
  let base : List (String × String) :=
    [("content-type", mediaLwsJson), ("content-digest", digest)]
  let signed : List (String × String) :=
    match signer, urlParts? p.inbox with
    | some s, some (scheme, authority, path) =>
        let params := signatureParams now s.keyId
        let sig := s.sign (signatureBase scheme authority path digest params).toUTF8
        [ ("signature-input", "sig1=" ++ params)
        , ("signature", "sig1=:" ++ Base64.encode sig ++ ":") ]
    | _, _ => []
  { id := p.id, url := p.inbox, headers := base ++ signed, body := p.body }

/-! ## Routing changes to subscribers -/

/-- Is change `c` in the scope of subscription `s`? A Move is when the
scope holds its old or its new path. -/
def changeInScope (s : Subscription) (c : Change) : Bool :=
  inScope s c.path || (match c.type with
    | .move o => inScope s o
    | _ => false)

/-- May subscription `s` hear of change `c`? It is live, the change is in
its scope, and its agent may read the resource "at the time the event
occurs": after the step for Create, Update and Move, before it for
Delete. -/
def eligible (canRead : Option String → σ → String → Bool) (pre post : σ) (now : Nat)
    (s : Subscription) (c : Change) : Bool :=
  live now s && changeInScope s c &&
    canRead s.owner (if c.type = .delete then pre else post) c.path

/-- Each subscription with the activities it may hear of, in change order;
subscriptions that hear of nothing are left out. -/
def routed {α : Type} (canRead : Option String → σ → String → Bool) (pre post : σ) (now : Nat)
    (subs : List Subscription) (cs : List (Change × α)) : List (Subscription × List (Change × α)) :=
  subs.filterMap (fun s =>
    let mine := cs.filter (fun x => eligible canRead pre post now s x.1)
    if mine.isEmpty then none else some (s, mine))

/-- **Delivery-time authorization.** Every activity routed to a
subscription is about a resource in the subscription's scope, the
subscription is live, and its agent may read the resource at the time of
the event (LWS §Subscription Authorization: "A server MUST NOT deliver a
notification about a resource that the subscriber is not authorized to read
at the time the event occurs"). -/
theorem routed_authorized {α : Type} {canRead : Option String → σ → String → Bool}
    {pre post : σ} {now : Nat} {subs : List Subscription} {cs : List (Change × α)}
    {s : Subscription} {mine : List (Change × α)} {x : Change × α}
    (hs : (s, mine) ∈ routed canRead pre post now subs cs) (hx : x ∈ mine) :
    live now s = true ∧ changeInScope s x.1 = true ∧
    canRead s.owner (if x.1.type = .delete then pre else post) x.1.path = true ∧
    s ∈ subs ∧ x ∈ cs := by
  unfold routed at hs
  obtain ⟨s', hs', he⟩ := List.mem_filterMap.mp hs
  dsimp only at he
  split at he
  · simp at he
  · simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := List.mem_filter.mp hx
    simp only [eligible, Bool.and_eq_true] at this
    exact ⟨this.2.1.1, this.2.1.2, this.2.2, hs', this.1⟩

/-- The activities waiting for subscription `id`, oldest first. -/
def heldOf (ns : NotifState) (id : String) : List Json :=
  (ns.held.filter (·.1 == id)).map (·.2)

/-- The deliveries of one step: number the changes, build each activity
once, route them, and make one pending delivery per subscription that
`admit` lets through, with the activities that waited for it first. The
activities of a subscription over its limit wait in `held`. -/
def emit (canRead : Option String → σ → String → Bool) (baseIri : String)
    (signer : Option Signer) (now : Nat) (pre post : σ) (changes : List Change)
    (ns : NotifState) (rate : Rate := {}) : NotifState × List Delivery :=
  if changes.isEmpty then (ns, []) else
  let published := isoDateTime now
  let acts := changes.zipIdx.map (fun (c, i) =>
    (c, activityJson baseIri (activityId ns.run (ns.seq + i)) published c))
  let seq1 := ns.seq + changes.length
  let groups := routed canRead pre post now ns.subs acts
  let decided : List (Subscription × Bool × List Json) := groups.map (fun (s, mine) =>
    let (send, s') := admit rate now s
    (s', send, mine.map (fun (x : Change × Json) => x.2)))
  let sends := (decided.filter (·.2.1)).map (fun (s', _, as_) => (s', heldOf ns s'.id ++ as_))
  let waits := decided.filter (fun x => !x.2.1)
  let held1 := (ns.held.filter (fun h => !sends.any (·.1.id == h.1))) ++
    waits.flatMap (fun (s', _, as_) => as_.map (s'.id, ·))
  let held2 := held1.drop (held1.length - heldLimit)
  let heldChanged := !waits.isEmpty || sends.any (fun x => !(heldOf ns x.1.id).isEmpty)
  let subs' := ns.subs.map (fun s => match decided.find? (·.1.id == s.id) with
    | some (s', _, _) => s'
    | none => s)
  let pend : List Pending := sends.zipIdx.map (fun ((s, as_), k) =>
    { id := "d" ++ toString (seq1 + k), subId := s.id, inbox := s.inbox
      body := toStringCompact (envelopeJson baseIri as_), attempt := 1 })
  ({ ns with seq := seq1 + sends.length, subs := subs', held := held2
             revision := if heldChanged then ns.revision + 1 else ns.revision
             pending := (pend.reverse ++ ns.pending).take pendingLimit },
   pend.map (deliveryOf signer now))

/-- The waiting activities whose window has ended: one batched envelope per
live subscription that `admit` lets through; the activities of a
subscription that is no longer live, or no longer exists, are dropped. -/
def flush (baseIri : String) (signer : Option Signer) (now : Nat) (rate : Rate)
    (ns : NotifState) : NotifState × List Delivery :=
  let waiting := ns.subs.filter (fun s => !(heldOf ns s.id).isEmpty)
  let dead := waiting.filter (fun s => !live now s)
  let ready := (waiting.filter (live now)).filterMap (fun s =>
    match admit rate now s with
    | (true, s') => some s'
    | (false, _) => none)
  let gone := (ready ++ dead).map (·.id)
  let orphans := ns.held.filter (fun h => !ns.subs.any (·.id == h.1))
  if gone.isEmpty && orphans.isEmpty then (ns, []) else
  let pend : List Pending := ready.zipIdx.map (fun (s, k) =>
    { id := "d" ++ toString (ns.seq + k), subId := s.id, inbox := s.inbox
      body := toStringCompact (envelopeJson baseIri (heldOf ns s.id)), attempt := 1 })
  ({ ns with subs := ns.subs.map (fun s => (ready.find? (·.id == s.id)).getD s)
             held := ns.held.filter (fun h => !gone.contains h.1 && ns.subs.any (·.id == h.1))
             seq := ns.seq + ready.length, revision := ns.revision + 1
             pending := (pend.reverse ++ ns.pending).take pendingLimit },
   pend.map (deliveryOf signer now))

/-- The seconds until the first window with waiting activities ends (at
least 1), or `none` when nothing waits. The host calls `lwsFlush` then. -/
def nextWake (now : Nat) (rate : Rate) (ns : NotifState) : Option Nat :=
  let ends := (ns.subs.filter (fun s => live now s && !(heldOf ns s.id).isEmpty)).map
    (fun s => Nat.max 1 (s.windowStart + rate.window - now))
  ends.foldl (fun acc e => some (match acc with | some a => Nat.min a e | none => e)) none

/-! ## Delivery outcomes (webhook suite §Notification Delivery) -/

/-- May a delivery that got this status succeed on a later attempt? No
answer (0), 408 Request Timeout, 425 Too Early, 429 Too Many Requests and
every 5xx. -/
def retryable (status : Nat) : Bool :=
  status == 0 || status == 408 || status == 425 || status == 429 || (500 ≤ status && status < 600)

private def updSub (ns : NotifState) (id : String) (f : Subscription → Subscription) : NotifState :=
  { ns with subs := ns.subs.map (fun s => if s.id == id then f s else s) }

/-- The answer to one attempt. 2xx acknowledges ("A 2xx response indicates
successful receipt") and clears the failure count. A retryable status
before the last attempt gives the next attempt and the seconds to wait
(1, then 2). 410 Gone deactivates the subscription at once; any other
failure counts, and `failureLimit` failures in a row deactivate it. An
unknown delivery id changes nothing. -/
def deliveryResult (signer : Option Signer) (now : Nat) (id : String) (status : Nat)
    (ns : NotifState) : NotifState × Option (Delivery × Nat) :=
  match ns.pending.find? (fun p => p.id == id) with
  | none => (ns, none)
  | some p =>
      let rest := ns.pending.filter (fun q => q.id != id)
      let ns1 := { ns with pending := rest }
      if 200 ≤ status && status < 300 then
        (updSub ns1 p.subId (fun s => { s with failures := 0 }), none)
      else if status == 410 then
        ({ updSub ns1 p.subId (fun s => { s with active := false }) with
           revision := ns.revision + 1 }, none)
      else if retryable status && p.attempt < maxAttempts then
        let p' := { p with attempt := p.attempt + 1 }
        ({ ns1 with pending := p' :: rest }, some (deliveryOf signer now p', 2 ^ (p.attempt - 1)))
      else
        let failures := ((ns.subs.find? (fun s => s.id == p.subId)).map (·.failures)).getD 0 + 1
        let off := failures ≥ failureLimit
        ({ updSub ns1 p.subId (fun s => { s with failures, active := s.active && !off }) with
           revision := if off then ns.revision + 1 else ns.revision }, none)

/-! ## The subscription endpoint -/

/-- The IRI of a subscription. -/
def subscriptionIri (baseIri id : String) : String :=
  iriOfPath baseIri (subscriptionsPath ++ id)

/-- The state of one subscription, as GET returns it. -/
def subscriptionJson (baseIri : String) (now : Nat) (s : Subscription) : Json :=
  .object (
    [ ("@context", .array [.string lwsProfile])
    , ("id", .string (subscriptionIri baseIri s.id))
    , ("type", .string webhookSubscriptionType)
    , ("subscription", .string (subscriptionIri baseIri s.id))
    , ("topic", .array (s.topics.map (fun t => Json.string (iriOfPath baseIri t))))
    , ("inbox", .string s.inbox) ] ++
    (match s.expires with
     | some e => [("expires", .string e)]
     | none => []) ++
    [ ("active", .bool (live now s)) ])

/-- The path of a topic IRI inside this storage, or `none`. -/
def topicPath? (baseIri t : String) : Option String :=
  if t.startsWith baseIri then
    let p := "/" ++ (t.drop baseIri.length).toString
    if validTarget p && !isSubscriptionPath p && p != storagePath then some p else none
  else none

/-- What a subscription request asks for, once it is read. -/
structure SubRequest where
  topics : List String
  inbox : String
  expires : Option String
  expiresAt : Option Nat

/-- Read a subscription request body (LWS §Subscription Request, webhook
suite §Creating a Webhook Subscription). The error is the status and the
detail of the refusal. -/
def readSubRequest (baseIri : String) (now : Nat) (body : ByteArray)
    (loops : String → Bool := fun _ => false) :
    Except (Nat × String) SubRequest := do
  let text ← (String.fromUTF8? body).elim (.error (400, "the request is not UTF-8")) .ok
  let j ← match parseJson text with
    | .ok j@(.object _) => .ok j
    | _ => .error (400, "the request is not a JSON object")
  let ty ← (j.getString? "type").elim
    (.error (400, "member \"type\" is required and is a string")) .ok
  if ty != webhookSubscriptionType then
    .error (400, "type \"" ++ ty ++ "\" is not a subscription type of this service")
  let ts ← (j.getArray? "topic").elim
    (.error (400, "member \"topic\" is required and is an array of URIs")) .ok
  if ts.isEmpty then .error (400, "member \"topic\" names no resource")
  let iris ← ts.mapM (fun t => match t with
    | .string s => .ok s
    | _ => .error (400, "every topic is a URI string"))
  let topics ← iris.mapM (fun t => (topicPath? baseIri t).elim
    (.error (400, "topic " ++ t ++ " is not a resource of this storage")) .ok)
  let inbox ← (j.getString? "inbox").elim
    (.error (400, "member \"inbox\" is required for a WebhookSubscription")) .ok
  if (urlParts? inbox).isNone then .error (400, "inbox is not an http or https URL")
  -- A delivery POSTed to a container of this storage would create a
  -- resource there, and that Create would be delivered again: refuse it.
  if inbox.startsWith baseIri then
    let (p, _) := splitTarget ("/" ++ (inbox.drop baseIri.length).toString)
    let p := String.ofList (p.toList.takeWhile (fun (c : Char) => c != '#'))
    if pathIsContainer p && !isSubscriptionPath p then
      .error (400, "inbox is a container of this storage: a delivery would create a resource and so another notification")
  -- This server under another host name, IP address or `localhost`
  -- (`InboxGuard.loops`, issue 915).
  if loops inbox then
    .error (400, "inbox names this server (its host, one of its addresses or localhost, at its port): a delivery would be a request to this server")
  let (expires, expiresAt) ← match j.field? "expires" with
    | none | some .null => .ok (none, none)
    | some (.string e) =>
        match parseRfc3339? e with
        | none => .error (400, "expires is not an RFC 3339 date-time")
        | some t =>
            if t ≤ now then .error (400, "expires is not in the future")
            else .ok (some e, some t)
    | some _ => .error (400, "expires is not an RFC 3339 date-time")
  .ok { topics := topics.eraseDups, inbox, expires, expiresAt }

/-- The subscriptions an agent sees: its own. -/
def ownedBy (agent : Option String) (ns : NotifState) : List Subscription :=
  ns.subs.filter (fun s => s.owner == agent)

/-- The listing of the endpoint, an LWS container of the agent's
subscriptions (webhook suite §Subscription Management), page `n` of size
`k`. -/
def listingJson (baseIri : String) (now : Nat) (items : List Subscription) (total : Nat) : String :=
  toStringCompact (.object
    [ ("@context", .string lwsProfile)
    , ("id", .string (iriOfPath baseIri subscriptionsPath))
    , ("type", .string "Container")
    , ("totalItems", .number (toString total))
    , ("items", .array (items.map (fun s =>
        let doc := toStringCompact (subscriptionJson baseIri now s)
        Json.object
          [ ("id", .string (subscriptionIri baseIri s.id))
          , ("type", .string "DataResource")
          , ("format", .string mediaLwsJson)
          , ("size", .number (toString doc.utf8ByteSize))
          , ("modified", .string (isoDateTime s.created)) ]))) ])

private def lwsJsonResponse (status : Nat) (doc : String) (extra : List (String × String) := [])
    (head : Bool := false) : Response :=
  ⟨status, [("content-type", mediaLwsJson)] ++ extra, if head then "" else doc, none⟩

/-- The subscription endpoint and its members. `canRead` is the access
check on the current store; `agent` is the authenticated agent. -/
def subscriptionsStep (canRead : Option String → String → Bool) (cfg : Config) (now : Nat)
    (agent : Option String) (r : Request) (path : String) (ns : NotifState) :
    Response × NotifState :=
  let base := cfg.baseIri
  let storageLink := ("link", renderLinks [{ target := storageIdOf base, rel := lwsStorageRel }])
  if path == subscriptionsPath then
    let allow := "GET, HEAD, OPTIONS, POST"
    match r.method with
    | "GET" | "HEAD" =>
        let (_, query0) := splitTarget r.path
        let query := if r.queryStr != "" then r.queryStr else query0
        let mine := ownedBy agent ns
        let k := cfg.pageSize
        let count := pageCount mine.length k
        let pageNo : Option Nat :=
          if query == "" then some 1 else pageOfQuery? query
        match pageNo with
        | none => (problem 404 "no page of the subscription listing has this name" path, ns)
        | some n =>
            if n == 0 || n > count then (problem 404 "the listing has no such page" path, ns) else
            let items := if paginated mine.length k then pageAt mine k (n - 1) else mine
            let pageLink (rel : String) (m : Nat) : Link :=
              { target := path ++ "?" ++ pageQuery m, rel }
            let links : List Link :=
              [{ target := storageIdOf base, rel := lwsStorageRel }] ++
              (if paginated mine.length k then
                 [pageLink "first" 1, pageLink "last" count] ++
                 (if n < count then [pageLink "next" (n + 1)] else []) ++
                 (if n > 1 then [pageLink "prev" (n - 1)] else [])
               else [])
            (lwsJsonResponse 200 (listingJson base now items mine.length)
               [("allow", allow), ("link", renderLinks links)] (r.method == "HEAD"), ns)
    | "OPTIONS" => (⟨204, [("allow", allow), ("accept-post", mediaLwsJson)], "", none⟩, ns)
    | "POST" =>
        let ct := (r.header? "content-type").map baseMedia
        if ct != some mediaLwsJson && ct != some "application/json" then
          (problem 415 "a subscription request is application/lws+json" path
            [("accept-post", mediaLwsJson)], ns)
        else match readSubRequest base now r.content (InboxGuard.loops cfg) with
          | .error (status, msg) => (problem status msg path, ns)
          | .ok q =>
              -- LWS §Subscription Authorization: read access to EVERY topic.
              match q.topics.find? (fun t => !canRead agent t) with
              | some t =>
                  (problem 403 ("the subscriber may not read " ++ iriOfPath base t) path, ns)
              | none =>
                  let id := "sub" ++ toString ns.seq
                  let s : Subscription :=
                    { id, owner := agent, topics := q.topics, inbox := q.inbox
                      expires := q.expires, expiresAt := q.expiresAt, created := now }
                  let iri := subscriptionIri base id
                  let doc := toStringCompact (.object (
                    [ ("@context", .array [.string lwsProfile])
                    , ("type", .string webhookSubscriptionType)
                    , ("subscription", .string iri) ] ++
                    (match q.expires with
                     | some e => [("expires", .string e)]
                     | none => [])))
                  (lwsJsonResponse 201 doc [("location", iri), storageLink],
                   { ns with subs := ns.subs ++ [s], seq := ns.seq + 1,
                             revision := ns.revision + 1 })
    | _ => (problem 405 "the subscription endpoint accepts GET, HEAD, OPTIONS and POST" path
              [("allow", allow)], ns)
  else
    let id := (path.drop subscriptionsPath.length).toString
    let allow := "GET, HEAD, OPTIONS, DELETE"
    match (ownedBy agent ns).find? (fun s => s.id == id) with
    | none => (problem 404 "no subscription of this subscriber has this name" path, ns)
    | some s =>
        match r.method with
        | "GET" | "HEAD" =>
            (lwsJsonResponse 200 (toStringCompact (subscriptionJson base now s))
               [("allow", allow), storageLink] (r.method == "HEAD"), ns)
        | "OPTIONS" => (⟨204, [("allow", allow)], "", none⟩, ns)
        | "DELETE" =>
            (⟨204, [], "", none⟩,
             { ns with subs := ns.subs.filter (fun x => x.id != id),
                       pending := ns.pending.filter (fun p => p.subId != id),
                       held := ns.held.filter (fun h => h.1 != id),
                       revision := ns.revision + 1 })
        | _ => (problem 405 "a subscription accepts GET, HEAD, OPTIONS and DELETE" path
                  [("allow", allow)], ns)

/-! ## The server step -/

open L4Factoidal.Solid.Server (Requester allowed aclGraphOf requiredMode targetsAcl
  authorizationSubject)

/-- The access check of notifications: Web Access Control read access over
the storage's ACL resources, or a `read` access grant
(`AccessPolicy.grantAllows`, at the store's clock, with no client: a grant
limited to one client application reaches no notification), which is the
policy `Authorization.decide` enforces; or everything in the development
mode. -/
def wacCanRead (S : Store σ) (cfg : Config) (a : Authorization.AuthzConfig)
    (who : Option String) (st : σ) (p : String) : Bool :=
  a.insecureNoAuth ||
    allowed S aclGraphOf cfg.baseIri st (authorizationSubject p) { webId := who }
      (requiredMode "GET" (targetsAcl p)) ||
    AccessPolicy.grantAllows S st a.access.grants who none (S.now st) "GET" p

/-- One request to a storage that offers notifications: authorization
(`Authorization.decide`), then the subscription endpoint or the storage
operation (`step`), then the deliveries the operation's changes cause.
`.inl (issuer, url)` asks the host to fetch an authorization server
document first. With no subscription, no change is computed. -/
def serverStep (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (signer : Option Signer) (now : Nat) (r : Request)
    (st : σ) (ns : NotifState) :
    Sum (String × String) (Response × σ × NotifState × List Delivery) :=
  match Authorization.decide V S cfg a now r st with
  | .fetch i u => .inl (i, u)
  | .respond resp => .inr (resp, st, ns, [])
  | .proceed agent =>
      let (path, _) := splitTarget r.path
      if cfg.notifications && isSubscriptionPath path && validTarget path then
        let (resp, ns') := subscriptionsStep (fun who p => wacCanRead S cfg a who st p)
          cfg now agent r path ns
        .inr (resp, st, ns', [])
      else
        let (resp, st') := step S { cfg with agent := agent } r st
        if !cfg.notifications || ns.subs.isEmpty then .inr (resp, st', ns, []) else
        let changes := changesOf S r resp st st'
        let (ns', ds) := emit (wacCanRead S cfg a) cfg.baseIri signer now st st' changes ns cfg.rate
        .inr (resp, st', ns', ds)

/-- The inbox host of a subscription request that the host must resolve
before the request is stepped (`InboxGuard.toResolve?`): only for an
authorized POST to the subscription endpoint, so an unauthorized client
makes the host resolve nothing. -/
def resolveNeeded? (V : JOSE.Verifiers) (S : Store σ) (cfg : Config)
    (a : Authorization.AuthzConfig) (now : Nat) (r : Request) (st : σ) : Option String :=
  let (path, _) := splitTarget r.path
  if !cfg.notifications || path != subscriptionsPath || r.method != "POST" then none else
  match Authorization.decide V S cfg a now r st with
  | .proceed _ =>
      match (String.fromUTF8? r.content).bind parseJson? with
      | some j => (j.getString? "inbox").bind (InboxGuard.toResolve? cfg)
      | none => none
  | _ => none

/-! ## Persistence -/

/-- The durable part of the state: the subscriptions and the counter. -/
def notifStateJson (ns : NotifState) : Json :=
  .object
    [ ("seq", .number (toString ns.seq))
    , ("subscriptions", .array (ns.subs.map (fun s => Json.object (
        [ ("id", .string s.id)
        , ("owner", match s.owner with | some o => .string o | none => .null)
        , ("topics", .array (s.topics.map Json.string))
        , ("inbox", .string s.inbox)
        , ("created", .number (toString s.created))
        , ("failures", .number (toString s.failures))
        , ("active", .bool s.active) ] ++
        (match s.expires, s.expiresAt with
         | some e, some t => [("expires", .string e), ("expiresAt", .number (toString t))]
         | _, _ => [])))))
    , ("held", .array (ns.held.map (fun (id, act) =>
        Json.object [("subscription", .string id), ("activity", act)]))) ]

private def natOf? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?
  | _ => none

/-- Read the durable part back. Every topic must be a valid storage path. -/
def notifStateOfJson (j : Json) : Except String NotifState := do
  let items ← (j.getArray? "subscriptions").elim (.error "notifications: no subscriptions") .ok
  let subs ← items.mapM (fun it => do
    let id ← (it.getString? "id").elim (.error "notifications: a subscription has no id") .ok
    let topics ← match it.getArray? "topics" with
      | some ts => ts.mapM (fun t => match t with
          | .string p => if validTarget p then .ok p
                         else .error "notifications: a topic is not a storage path"
          | _ => .error "notifications: a topic is not a string")
      | none => .error "notifications: a subscription has no topics"
    let inbox ← (it.getString? "inbox").elim (.error "notifications: a subscription has no inbox") .ok
    .ok ({ id, owner := it.getString? "owner", topics, inbox
           expires := it.getString? "expires", expiresAt := natOf? it "expiresAt"
           created := (natOf? it "created").getD 0, failures := (natOf? it "failures").getD 0
           active := it.field? "active" != some (.bool false) } : Subscription))
  let held : List (String × Json) := ((j.getArray? "held").getD []).filterMap (fun h =>
    match h.getString? "subscription", h.field? "activity" with
    | some id, some act => some (id, act)
    | _, _ => none)
  .ok { subs, seq := (natOf? j "seq").getD 0, held := held.drop (held.length - heldLimit) }

end L4Factoidal.LWS.Notifications
