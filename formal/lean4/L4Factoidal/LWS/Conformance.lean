/-
L4Factoidal.LWS.Conformance — the MUST-statement registry of the Linked Web
Storage Protocol 1.0 Core.

The draft defines no test suite; its conformance is the list of "MUST"
statements it makes, which is what this registry is. Every statement is
quoted VERBATIM from
https://w3c.github.io/lws-protocol/lws10-core/ as read 2026-09-06, with the
section it appears in.

The draft's `Operations`, `Containers`, `Discovery`, `Authentication` and
`Authorization` sections are headings with no body, so the draft states no
status codes and no HTTP binding. Rows whose engine behaviour needs a
binding say `LWS core §Operations (todo); binding from Solid Protocol
v0.11.0 §N` in their `binding` field, so the day the draft fixes its own
binding the difference is exactly those rows.

`L4Factoidal.LWS.Tests` carries one `#guard` per row whose status is
`guarded`; `Harness/LwsProbe.lean` prints the counts.
-/
import L4Factoidal.LWS.Model

namespace L4Factoidal.LWS.Conformance

/-- How a requirement is decided. -/
inductive Status where
  /-- A Lean theorem discharges it. The argument names the theorem. -/
  | proved (theoremName : String)
  /-- A `#guard` evaluates it at build time. The argument names the guard. -/
  | guarded (testName : String)
  /-- The decision needs bytes, a socket, a clock or a token the Lean side
      does not hold; a host test decides it. -/
  | hostVerified (hostTest : String)
  /-- Not decided yet. The argument says what is missing. -/
  | «open» (why : String)
deriving Repr, DecidableEq, Inhabited

def Status.label : Status → String
  | .proved _ => "proved"
  | .guarded _ => "guarded"
  | .hostVerified _ => "host-verified"
  | .«open» _ => "open"

def Status.detail : Status → String
  | .proved t => t
  | .guarded t => t
  | .hostVerified t => t
  | .«open» w => w

/-- One row of the registry. -/
structure Requirement where
  /-- A stable identifier. `lws-core-NN`. -/
  id        : String
  /-- The section of the source document the statement appears in. -/
  section_  : String
  /-- The statement, verbatim. -/
  statement : String
  /-- The Lean module that decides it. -/
  module    : String
  /-- Where the HTTP binding comes from, when the draft has none. -/
  binding   : String := ""
  status    : Status
deriving Repr, Inhabited

/-- The registry. -/
def registry : List Requirement :=
[ { id := "lws-core-01"
  , section_ := "Resource Access"
  , statement := "A LWS Server is an HTTP server [RFC9112] that complies with all of the relevant \"MUST\" statements in this specification."
  , module := "L4Factoidal.LWS.Operations"
  , binding := "the conformance class itself; every other row is one of its MUST statements"
  , status := .«open» "the draft's Operations, Containers, Discovery, Authentication and Authorization sections have empty bodies, so the class is not yet closed" }
, { id := "lws-core-02"
  , section_ := "Resource Access"
  , statement := "An LWS Client is an HTTP client [RFC9112] that complies with all of the relevant \"MUST\" statements in this specification."
  , module := "L4Factoidal.Solid.Client"
  , binding := "the client conformance class; the Solid client modules are its only implementation here"
  , status := .«open» "same empty sections as lws-core-01" }
, { id := "lws-core-03"
  , section_ := "For Editors (CG-to-ED delta)"
  , statement := "HTTP Server MUST generate a Last-Modified header field in response to GET and HEAD requests."
  , module := "L4Factoidal.LWS.Operations.step"
  , binding := "no binding needed: the statement names the HTTP header field itself"
  , status := .guarded "lwsGuardLastModifiedOnGet, lwsGuardLastModifiedOnHead" }
, { id := "lws-core-04"
  , section_ := "For Editors (CG-to-ED delta)"
  , statement := "The PATCH ?insertions formulae MUST NOT contain blank nodes."
  , module := "L4Factoidal.LWS.Patch.wellFormed"
  , binding := "LWS core §Operations (todo); status code 422 from Solid Protocol v0.11.0 §5.3.1"
  , status := .guarded "lwsGuardInsertionsRefuseBlankNodes" }
, { id := "lws-core-05"
  , section_ := "Terminology"
  , statement := "container — an LWS resource that is able to enumerate a collection of LWS resources, conforming to the conventions described in Section 8. Containers."
  , module := "L4Factoidal.LWS.Operations.containedPaths"
  , binding := "LWS core §Containers (todo); enumeration by containment triples from Solid Protocol v0.11.0 §4.2"
  , status := .guarded "lwsGuardContainerEnumerates" }
, { id := "lws-core-06"
  , section_ := "Terminology"
  , statement := "storage root — a container at the root of a containment hierarchy of a storage. The storage root is the only LWS resource that does not have a parent in the LWS containment hierarchy nor a primary resource."
  , module := "L4Factoidal.LWS.Model.parent?"
  , binding := "LWS core §Resource Identification (todo); slash semantics from Solid Protocol v0.11.0 §3.1"
  , status := .proved "L4Factoidal.LWS.Tests.rootHasNoParent" }
, { id := "lws-core-07"
  , section_ := "Terminology"
  , statement := "auxiliary resource — an LWS resource that plays a particular role with respect to a LWS resource, called its primary resource, and whose lifetime is bound to the primary resource."
  , module := "L4Factoidal.Solid.Server.Auxiliary"
  , binding := "LWS core §Operations (todo); the delete rule from Solid Protocol v0.11.0 §4.3"
  , status := .proved "L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject" }
, { id := "lws-core-08"
  , section_ := "Terminology"
  , statement := "Auxiliary resources are discovered using web links [RFC8288] of a specific type (see Section )."
  , module := "L4Factoidal.LWS.Discovery.discoveryLinks"
  , binding := "LWS core §Discovery (todo); link relations acl and describedby from Solid Protocol v0.11.0 §4.3"
  , status := .guarded "lwsGuardAuxiliaryLinksAdvertised" }
, { id := "lws-core-09"
  , section_ := "Terminology"
  , statement := "linkset resource — a type of auxiliary resource whose representation conforms to [RFC9264]."
  , module := "L4Factoidal.LWS.Model.ResourceKind"
  , binding := "LWS core §Operations (todo)"
  , status := .«open» "the kind and its linkset link relation exist; RFC 9264 linkset serialisation is not implemented" }
, { id := "lws-core-10"
  , section_ := "Terminology"
  , statement := "metadata resource — an auxiliary resource, managed by a storage, that describes an LWS resource and conforms to the conventions described in TBD."
  , module := "L4Factoidal.LWS.Model.ResourceKind"
  , binding := "LWS core: the conventions are marked TBD in the draft"
  , status := .«open» "the draft marks the metadata-resource conventions TBD; the kind and its describedby link exist" }
, { id := "lws-core-11"
  , section_ := "Resource Access"
  , statement := "An operation is any of the following actions that can be performed on a served resource: create resource, read resource, update resource, delete resource."
  , module := "L4Factoidal.LWS.Operations.step"
  , binding := "LWS core §Operations (todo); methods and status codes from Solid Protocol v0.11.0 §5"
  , status := .guarded "lwsGuardCreateReadUpdateDelete" }
, { id := "lws-core-12"
  , section_ := "Resource Access"
  , statement := "success - the operation is believed to have completed. This may be accompanied by a resource representation conveying the contents of a served resource. A success response is not defined for the create resource operation. See instead created."
  , module := "L4Factoidal.LWS.Operations.step"
  , binding := "LWS core §Operations (todo); 200/201/204 from Solid Protocol v0.11.0 §5"
  , status := .guarded "lwsGuardCreatedIsNotSuccess" }
, { id := "lws-core-13"
  , section_ := "Resource Access"
  , statement := "not permitted"
  , module := "L4Factoidal.Solid.Server.WAC"
  , binding := "LWS core §Authorization (todo); 401 and 403 from Solid Protocol v0.11.0 §2.1 and Web Access Control §5.3"
  , status := .guarded "solidGuardWacDenies" }
, { id := "lws-core-14"
  , section_ := "Resource Access"
  , statement := "unknown requester"
  , module := "L4Factoidal.Solid.Server.Auth"
  , binding := "LWS core §Authentication (todo); Solid-OIDC binding from Solid Protocol v0.11.0 §10.1 and RFC 9449"
  , status := .guarded "solidGuardSolidOidcDpop" }
, { id := "lws-core-15"
  , section_ := "Authentication"
  , statement := "LWS makes use of user authentication as defined in specifications for OpenID Connect, SAML 2.0, and self-signed controlled identifiers (CIDs), for example."
  , module := "L4Factoidal.Solid.Server.Auth"
  , binding := "LWS core §Authentication (todo); the sibling drafts lws10-authn-openid, lws10-authn-saml, lws10-authn-ssi-cid are separate documents"
  , status := .guarded "solidGuardSolidOidcDpop" }
, { id := "lws-core-16"
  , section_ := "Notifications"
  , statement := "notification — a message describing an event that has occurred on a resource."
  , module := "L4Factoidal.LWS.Notifications"
  , binding := "LWS core §Notifications (w3c/lws-protocol 9a08ff65); LWS 1.0 Notification Suite: Webhooks"
  , status := .guarded "lwsGuardNotificationsDelivered" }
, { id := "lws-core-17"
  , section_ := "Access Requests and Grants"
  , statement := "access grant — a data object created by a storage controller, expressing an ability for an agent to perform specific actions on storage resources within certain defined constraints."
  , module := "L4Factoidal.LWS.AccessPolicy.grantsPermit"
  , binding := "LWS core §Access Requests and Grants (w3c/lws-protocol 9a08ff65): the grant endpoint, enforced by Authorization.decide"
  , status := .proved "L4Factoidal.LWS.AccessPolicy.grantsPermit_sound" }
, { id := "lws-core-18"
  , section_ := "Terminology"
  , statement := "storage description — an LWS resource, conforming to the requirements of a W3C Controlled Identifier document [CID-1.0], that describes a storage along with its services and capabilities."
  , module := "L4Factoidal.LWS.Discovery.storageDescriptionPath"
  , binding := "LWS core §Discovery (todo); the storageDescription link relation from Solid Protocol v0.11.0 §4.1"
  , status := .«open» "the link is advertised; the description document does not yet conform to CID 1.0" }
, { id := "lws-core-19"
  , section_ := "Moving Resources"
  , statement := "On a successful update, the server MUST atomically remove the resource from the items list of its former parent container and add it to the items list of the destination container."
  , module := "L4Factoidal.LWS.Move.move"
  , binding := "LWS core §Moving Resources (w3c/lws-protocol 9a08ff65): JSON Patch of the up link in the linkset resource"
  , status := .proved "L4Factoidal.LWS.move_tree" }
-- LWS Search and Type Index Services (lws10-index, w3c/lws-protocol 9a08ff65,
-- https://github.com/danbri/factoidal/issues/912). `L4Factoidal.LWS.Search`.
, { id := "lws-index-01"
  , section_ := "lws10-index: Discovery"
  , statement := "A storage that supports one of these services MUST advertise it with a service object in the service array of its storage description resource: the entry for the Type Index Service MUST have a type equal to TypeIndexService, and the entry for the Type Search Service MUST have a type equal to TypeSearchService."
  , module := "L4Factoidal.LWS.Binding.storageDescription"
  , status := .guarded "L4Factoidal.LWS.SearchTests.lwsGuardIndexDiscovery" }
, { id := "lws-index-02"
  , section_ := "lws10-index: QUERY [TypeSearchService]"
  , statement := "The type key is the mandatory baseline and MUST be supported by every server that implements the TypeSearchService."
  , module := "L4Factoidal.LWS.Search.searchStep"
  , status := .guarded "L4Factoidal.LWS.SearchTests.lwsGuardTypeSearch" }
, { id := "lws-index-03"
  , section_ := "lws10-index: Errors"
  , statement := "A request body that is not well-formed application/lws-query+json, or whose type is not an array, or any of whose elements is neither a string nor a non-empty array of strings, MUST be rejected with 400 (Bad Request)."
  , module := "L4Factoidal.LWS.Search.parseFilter"
  , status := .guarded "L4Factoidal.LWS.SearchTests.lwsGuardSearchErrors" }
, { id := "lws-index-04"
  , section_ := "lws10-index: Security and Authorization"
  , statement := "Unauthorized entries MUST be omitted entirely."
  , module := "L4Factoidal.LWS.Search.searchAnswer"
  , status := .proved "L4Factoidal.LWS.Search.searchAnswer_authorized" }
, { id := "lws-index-05"
  , section_ := "lws10-index: Security and Authorization"
  , statement := "A server MAY maintain a derived index for performance, but it MUST apply current authorization as a filter over that index on every request."
  , module := "L4Factoidal.LWS.Search.serverStep"
  , status := .guarded "L4Factoidal.LWS.SearchTests.lwsGuardSearchAuthorized" }
, { id := "lws-index-06"
  , section_ := "lws10-index: Type and Relation Derivation"
  , statement := "When a server enriches the type index from resource content, the types it surfaces MUST be treated identically to those derived from Link headers for the purposes of indexing, search, and authorization filtering."
  , module := "L4Factoidal.LWS.TypeIndex.entryFacts"
  , status := .proved "L4Factoidal.LWS.Search.ixSearch_eq_specSearch" }
, { id := "lws-index-07"
  , section_ := "lws10-index: QUERY (a results resource; ANTICIPATORY AND UNSTABLE, off by default, issue 922)"
  , statement := "this specification does not define such a resource; a server that nonetheless exposes one MUST subject it to the same authorization filtering on every access [...]"
  , module := "L4Factoidal.LWS.SearchResults.resultsAnswer"
  , status := .proved "L4Factoidal.LWS.SearchResults.resultsAnswer_authorized" }
, { id := "lws-index-08"
  , section_ := "lws10-index: QUERY (a results resource; ANTICIPATORY AND UNSTABLE, off by default, issue 922)"
  , statement := "a server that nonetheless exposes one [...] MUST prevent its reuse across clients."
  , module := "L4Factoidal.LWS.SearchResults.resultsGet"
  , status := .proved "L4Factoidal.LWS.SearchResults.resultsGet_creator_only" }
-- LWS core §Access Requests and Grants (w3c/lws-protocol 9a08ff65,
-- https://github.com/danbri/factoidal/issues/913). `L4Factoidal.LWS.AccessGrants`.
, { id := "lws-access-01"
  , section_ := "Access Requests and Grants: Discovery"
  , statement := "When such support is advertised, a service object describing an endpoint for access requests MUST have a type equal to the string AccessRequestService, and a service object describing an endpoint for access grants MUST have a type equal to the string AccessGrantService."
  , module := "L4Factoidal.LWS.Binding.storageDescription"
  , status := .guarded "L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessDiscovery" }
, { id := "lws-access-02"
  , section_ := "Access Requests and Grants: Protocol"
  , statement := "A successful POST operation MUST respond with a Location header set to the URL of the new resource."
  , module := "L4Factoidal.LWS.AccessGrants.accessStep"
  , status := .guarded "L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessCreate" }
, { id := "lws-access-03"
  , section_ := "Access Requests and Grants: Constraints"
  , statement := "When multiple constraint objects are present, all of them MUST be satisfied."
  , module := "L4Factoidal.LWS.AccessPolicy.policyPermits"
  , status := .guarded "L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessConstraints" }
, { id := "lws-access-04"
  , section_ := "Access Requests and Grants"
  , statement := "When an access grant is created or revoked (deleted), it is the responsibility of the server to adjust any underlying access policy to account for the change."
  , module := "L4Factoidal.LWS.AccessPolicy.revoke"
  , status := .proved "L4Factoidal.LWS.AccessPolicy.grantsPermit_revoke" }
, { id := "lws-access-05"
  , section_ := "Access Requests and Grants: Temporal Constraints"
  , statement := "The gteq operator defines the start of the window and the lteq operator defines the end."
  , module := "L4Factoidal.LWS.AccessPolicy.satisfied"
  , status := .proved "L4Factoidal.LWS.AccessPolicy.recordPermits_expired" }
, { id := "lws-access-06"
  , section_ := "Access Requests and Grants: Protocol"
  , statement := "A storage controller creates an access grant by submitting a POST request to the access grant endpoint."
  , module := "L4Factoidal.LWS.AccessGrants.accessStep"
  , status := .proved "L4Factoidal.LWS.AccessGrants.accessStep_grant_needs_controller" }
]

/-! ## Counting -/

def isProved   (r : Requirement) : Bool := match r.status with | .proved _ => true | _ => false
def isGuarded  (r : Requirement) : Bool := match r.status with | .guarded _ => true | _ => false
def isHost     (r : Requirement) : Bool := match r.status with | .hostVerified _ => true | _ => false
def isOpen     (r : Requirement) : Bool := match r.status with | .«open» _ => true | _ => false

def counts : Nat × Nat × Nat × Nat :=
  ( (registry.filter isProved).length
  , (registry.filter isGuarded).length
  , (registry.filter isHost).length
  , (registry.filter isOpen).length )

/-- Every row is decided one way or another, and the four counts add up to
the registry's length. Stated so a row added with a mistyped status cannot
disappear from the score. -/
theorem countsTotal :
    counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2 = registry.length := by
  rfl

end L4Factoidal.LWS.Conformance
