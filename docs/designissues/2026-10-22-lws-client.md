# The LWS client: one Lean state machine, three hosts (2026-10-22)

Tracking: https://github.com/danbri/factoidal/issues/917. Order: the owner's
2026-10-22 decision in CLAUDE.md, "Order after LWS storage stage 2" (item 3).
Server side and the rest of LWS: `skills/lws-solid/SKILL.md`,
`docs/designissues/2026-10-21-lws-overview.md`.

Sources, read 2026-10-22: lws10-core, lws10-index and
lws10-notifications-webhook at w3c/lws-protocol commit
9a08ff65a6670cc5d308ed5e531032f23af30fcc (2026-10-19); the Touchstone client
rules `definitions/lws10/clients/*.yamlld` (53 rules) at
ebremer/touchstone commit 1060872.

## Decision

Every client decision is made in Lean, in one pure function:

```
LWS.Client.step : Verifiers → ClientState → Event → ClientState × Action
Event  := start | response (status, headers, body bytes) | transportError
Action := fetch Req | done result | fail error
```

The caller says WHAT it wants (an `Op`: read, create, update, list, search,
subscribe, ...). `step` says which HTTP request to send next, reads each
answer, and ends with `done` or `fail`. The host is a loop: call `step`, send
the request it names with the `fetch` it was given, give the answer back.
The host reads no header, composes no URL and picks no media type
(iron rule 7, anti-pattern 36). The same machine serves the npm API, the CLI
and the wasm ABI.

The state is a JSON document that the host carries between calls; the wasm
ops are stateless. Bodies cross the string ABI as `bodyBase64` (RFC 4648 §4)
in both directions. `callBlobIO` is not used, because each step has a body in
at most one direction and the bodies of a client are small; a large upload is
a later change to one op, recorded here.

## Requirements and where each one is decided

| Draft section | Statement (verbatim) | Lean | Touchstone rule |
| --- | --- | --- | --- |
| lws10-core §Authorization, Discovery Validation by a Client | "Before requesting an access token, a client MUST perform the following checks ... If any check fails, the client MUST NOT use the discovered values to request an access token." (resource_metadata same scheme and authority; metadata `resource` identical to the requested URI; StorageRoot `serviceEndpoint` same scheme and authority) | `Client.Auth.validated`, `step_no_token_request_without_validation` | client-token-after-discovery-checks |
| same, Authorization Server Metadata | "This metadata resource MUST be available at a URL with the path /.well-known/lws-configuration." (RFC 8414 §3.1 insertion form) | `Client.Wire.asMetadataUrl` | |
| same, Token Exchange | "The resource parameter is REQUIRED ... The supplied value MUST be the URI of the storage that contains the requested resource, as provided in the Link header of an unauthorized response." and "The subject_token parameter is REQUIRED." | `Client.Auth.tokenRequest` | client-token-exchange-resource, client-token-exchange-subject-token, client-saml-token-type-saml2 |
| same, Presentation | "A client MUST present an access token to a storage server using the Authorization header with an authentication scheme as defined in [RFC6750]." | `Client.Machine.attachToken` | client-token-in-authorization-header |
| §Create Resource | "To create a Container, the client MUST include a Link header with rel="type" pointing to the Container type" | `Client.Requests.createReq` | client-create-container-type-link |
| §Create Resource | "Server-managed metadata MUST be generated automatically by the server upon creation and MUST NOT be overridden by client-provided links." (a client link with a server-managed relation is refused before sending) | `Client.Requests.clientLinksOk` | client-create-no-server-managed-links |
| §Create Resource | "Repeating it may create duplicates; clients SHOULD avoid unintentional retries or use unique identifiers/checks to prevent this." | phase `createCheck`, `step_no_blind_create_retry` | client-no-blind-retry-of-create |
| §Update Resource | "Clients SHOULD use conditional requests as defined in [RFC9110] to avoid overwriting concurrent changes." | `Precondition`, phase `tagRead`, `step_write_precondition` | client-put-conditional, client-linkset-write-conditional |
| §Update Resource | "clients MAY include Link headers in the PUT/PATCH request to the resource URI and specify the preference 'Prefer: set-linkset'" | `Client.Requests.updateReq` (Link implies Prefer) | client-combined-update-prefer-set-linkset |
| §Delete Resource | "Clients MUST use the Depth: infinity header to request for a recursive delete" and "Clients MAY include an If-Match header with an ETag" | `Client.Requests.deleteReq` | client-delete-container-depth, client-delete-conditional |
| §Metadata | "Clients SHOULD NOT assume support for PUT or specific patch formats unless they are advertised in the resource headers and MUST handle 405 Method Not Allowed or 415 Unsupported Media Type responses gracefully." | phases `linksetMeta`, `linksetRecheck`; `step_no_repeat_after_refusal` | client-linkset-put-only-when-advertised, client-linkset-patch-format-advertised, client-no-repeat-after-405-415 |
| §Moving Resources | "A client moves a resource by applying a partial update to the resource's linkset resource, replacing the target of the up link" and "Clients MUST NOT assume that the up link is modifiable in the absence of this capability." | op `move` | |
| §Pagination | "rel="next": ... MUST be present when there are subsequent pages." (the client follows `next`, builds no page URL) | phase `paging`, `walk_concat`, `walk_members_once` | client-page-urls-issued, client-member-urls-issued |
| §Notifications, Subscription | `type`, `topic`, `inbox` of a webhook subscription, POSTed as `application/lws+json` | `Client.Requests.subscribeReq` | client-subscription-media-type, -type, -topic, -inbox, -own-inbox |
| lws10-notifications-webhook §5.2 Signature Verification | "The keyid value MUST be a URL with a fragment component." and "The id property of the top-level document map MUST match the storage identifier." | op `verifyNotification` | client-inbox-acknowledges-genuine-delivery, -refuses-unpublished-key, -refuses-altered-body, -refuses-keyid-without-fragment, -refuses-foreign-key-document |
| §Access Requests and Grants | the data model (`@context`, `type`, `storage`, `access`, policy `type`, `action`, `assignee`, `target`, `constraint`, `inbox`) | `Client.Requests.accessDoc` | the 11 client-access-* rules |
| lws10-index §Type Search | "The query format is identified by the request's Content-Type header field, which MUST be present", "Clients MUST NOT assume read-your-writes consistency", page refused with 404 or 410: restart | op `search`, phase `searchPage` | client-query-content-type, client-query-baseline-after-415, client-restart-after-refused-page |

## Retry rules (all in Lean)

* 412 Precondition Failed: read the ETag again and resend only when the
  caller set `retry412 > 0`; the count goes down by one each time. Otherwise
  `fail {code: "preconditionFailed"}`.
* 405 or 415 from a linkset: never the same request again. Read the linkset
  again (`linksetRecheck`) and use the other method only if that answer
  advertises it and the caller's change can be expressed in it; otherwise
  `fail`.
* 5xx or a transport error after a create POST: never the same POST again.
  Read the container (`createCheck`) and end with `fail {code:
  "createOutcomeUnknown"}` with that listing, so the caller decides.
* A search page refused with 404 or 410: send the QUERY again, once.
* 401 with a token attached: drop the token, validate and exchange again,
  at most twice per operation.

## Theorems

In `L4Factoidal/LWS/Client/Theorems.lean`, imported from the build root:

* `walk_concat`: over any page source (`PageSource`: `count` pages, `next n =
  some (n+1)` below `count`, `none` at `count`), following `next` from page 1
  collects the concatenation of every page.
* `walk_listedMembers` and `walk_members_once`: instantiated with the
  server's own pages (`Operations.pageItems`, `orderedMemberPaths`), the walk
  gives `listedMembers`, and every member path occurs exactly once.
* `step_write_precondition`: for every state and event, a write request of
  the operation (PUT, PATCH, DELETE, or a POST to a linkset) that `step`
  emits carries the header of the precondition the caller asked for.
* `step_no_token_request_without_validation`: for every state and event, a
  token exchange request that `step` emits comes with a validation record
  in the next state whose three checks hold over the recorded values (the
  requested URI, the `resource_metadata` URL, the metadata `resource`, the
  StorageRoot endpoint), and its `resource` is the storage of that record.
* `step_no_blind_create_retry`: after a create POST answered 5xx or a
  transport error, the next action is not the same POST.
* `step_no_repeat_after_refusal`: after a 405 or 415, the next action is not
  the same request.

The four `step_*` theorems hold because `step` ends with `enforce`, a check
of the action against the state, which turns a violating action into `fail`.
The theorems say that no state and no event can make `step` emit a
violating request. The `#guard`s in `Client/Tests.lean` show that the
ordinary flows never reach the refusal of `enforce`.

## Hosts

* npm `@factoidal/core/lws/client`: `createLwsClient({ fetch, engine,
  subjectToken, subjectTokenType, maxSteps })`. `fetch` is any function with
  the WHATWG signature (Node, a browser, or a `fetch` carried over XMPP).
  Methods mirror the ops. `createInbox` is an HTTP receiver whose only
  logic is to call `verifyNotification` and write the status it gives.
* CLI `factoidal lws-client <op> URL [options]`.
* wasm ops `lwsClientStart(opJson, sessionJson)` and
  `lwsClientStep(stateJson, eventJson)`: `{ok, state, action}`.

## Gaps (each has an expected failure)

* CID self-issued credentials (10 authentication rules) need ES256 signing,
  which https://github.com/danbri/factoidal/issues/916 adds.
* OpenID sign-in (authorization code flow with PKCE) for
  `client-oidc-token-type-id-token`: the client takes an ID Token from the
  caller, but has no sign-in of its own. Issue to open; until then the row
  names https://github.com/danbri/factoidal/issues/917.
