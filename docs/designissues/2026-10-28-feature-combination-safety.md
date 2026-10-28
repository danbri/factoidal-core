# Feature combinations: invariants, where they are enforced, and the checks to add

Date: 2026-10-28. Issue: https://github.com/danbri/factoidal/issues/1120
(safety of feature combinations). Related:
https://github.com/danbri/factoidal/issues/1107 (HTTP over XMPP),
https://github.com/danbri/factoidal/issues/1108 (WebDAV login),
https://github.com/danbri/factoidal/issues/1119 (WebDAV failed-login limit),
https://github.com/danbri/factoidal/issues/1121 (MCP over XMPP),
https://github.com/danbri/factoidal/issues/1035 (network retrieval records).

Owner, 2026-10-28, verbatim: "Thanks for your care re open proxy. We will need
careful documentation and theorems to ensure that subtle combinations of these
features are not disasterous."

EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.

## 1. Scope and method

Each surface has its own guard. A combination of surfaces can open a path that
no single surface opens. This record lists, for each combination that can
interact: the path that an attacker or a mistake can take, the invariant that
must hold, where the code enforces it today (file:line or theorem), and the
check to add (a Lean theorem, stated as a Lean-like proposition, or a test that
fails when the invariant breaks).

Code read:

- Branch `wip-1108` at `144b41aa` (the WebDAV login, issue 1108), and
  `origin/main` at `e655516c` for `formal/lean4/L4Factoidal/XMPP/HttpOverXmpp.lean`
  (stage 1 of issue 1107, commit `d32afb6d`), which the `wip-1108` checkout
  does not have.
- Two pieces of uncommitted work, read as they stood on 2026-10-28; their line
  numbers will move:
  - the failed-login limit of issue 1119 (`Login.lean` `Limits`, `Failures`,
    `clientPrefix`, `loginKeys`), branch `rl-1119`;
  - step 1 of `webdav-serve --xmpp` (`Wasm/Ops/XmppClient.lean`,
    `L4Factoidal/XMPP/ClientStream.lean`, the `plan`/`finish` split of
    `HttpOverXmpp.step`), branch `xmpp-step1`.

Method: the module headers, the definitions on each request path, the theorem
statements, and `grep` over `formal/lean4` and `npm/factoidal` for the guards
named below (private addresses, `Host`, `Origin`, CORS credentials, login,
rate limits, TLS). No build or test was run. Limits of the method (anti-pattern
28): a "not found" below means that these searches found no guard. It does not
prove that no guard exists. The Solid server (`L4Factoidal/Solid/Server`) and
the F\* tree were not read. Planned surfaces (native `httpx://`, raw LWS over
XMPP, forwarding, MCP) have no code. For them, this record states the invariant
that the first implementation must meet.

## 2. Inventory of surfaces

| Surface | Host (npm) | Lean decisions | Guards found |
|---|---|---|---|
| `lws-serve` | `npm/factoidal/lws/server.mjs` | `Wasm/Ops/Lws.lean`, `L4Factoidal/LWS/*` | authorization unless `--insecure-no-auth` (`bin/factoidal.mjs:1957-1966`, warning `:2039`); no trusted issuer means no valid token (`validateToken_no_issuers`, `LWS/Authorization.lean:597`); only a configured issuer is fetched (`Authorization.lean:306`, `:515`); audience is `storageIri` (`Authorization.lean:186`, `:270`) |
| `lws-serve --authz` | same | `Authz/Mount.lean` `mountedOn` | the issuer is the storage root, resources `[storageIri]`; `--allow-private-fetch` passed through (`bin/factoidal.mjs:1977`) |
| CORS (`--cors-origin`, `--no-cors`, default echo) | `bin/factoidal.mjs:1819-1827` | `LWS/Cors.lean`, `HTTP/Cors.lean` | no `Access-Control-Allow-Credentials` (`LWS/Cors.lean:77`, `#guard` `:147`; `HTTP/Cors.lean:91`) |
| Webhook notifications | `lws/server.mjs:386-419` (`deliver`, `redirect: 'manual'`) | `LWS/Notifications.lean`, `LWS/InboxGuard.lean` | inbox is http(s) (`Notifications.lean:956`); inbox not this server (`:967`, `InboxGuard.loops` `:219`); per-subscription rate (`admits_le` `:621`, `admit_count_le` `:650`); only readers of a topic hear of it (`routed_authorized` `:775`) |
| Access requests and grants | same | `LWS/AccessGrants.lean` | grant inboxes: http(s) and not under `baseIri` (`AccessGrants.lean:273-278`); controller inbox from configuration (`:302-303`) |
| `authz-serve` and its fetches | `npm/factoidal/authz/server.mjs` | `Authz/Server.lean`, `Authz/Fetch.lean` | https only unless `allowHttp` (`lookup_http_refused`, `Fetch.lean:209`); private addresses refused unless `allowPrivateFetch` (`privateAddr` `:48`, `chooseAddress` `:121`, `chooseAddress_refuses_private` `:196`); the host connects to the address the engine chose (`authz/server.mjs:126-141`); token audience exactly `[resource]` (`issueToken_audience_exact`, `Authz/Theorems.lean:73`); resource is configured (`tokenRequest_resource` `:92`) |
| LWS client (`legacyChallenge`, `requireHttps`, tokens, subject tokens) | `npm/factoidal/lws/client.mjs` (`redirect: 'manual'`, `:200`) | `LWS/Client/Machine.lean` | `step_requireHttps` (`LWS/Client/Theorems.lean:211`); `step_no_token_request_without_validation` (`:243`); `attachToken_realm` (`:372`); both options off by default (`Machine.lean:333`, `:336`) |
| `webdav-serve`, local mounts | `npm/factoidal/webdav/server.mjs` | `WebDAV/Local.lean`, `WebDAV/Server.lean` | the mount is opened with `insecureNoAuth` (`Wasm/Ops/WebDAV.lean:249`); a local mount takes no `auth` (`WebDAV/Config.lean:207`); read-only mounts refuse writes before any storage operation (`precheck` `WebDAV/Server.lean:630`, `refused_keeps_state` `:772`) |
| `webdav-serve`, remote `lws` mounts | same | `WebDAV/Remote.lean` | credentials `did-key` or `bearer` (`sessionOf` `Remote.lean:129`); mount URL is http or https (`Config.lean:177`, `:226`) |
| `webdav-serve --users`, TLS | same | `WebDAV/Login.lean`, `Wasm/Ops/WebDAV.lean` | Basic only on TLS or loopback (`transportAllowsBasic` `Login.lean:220`, checked at start `Wasm/Ops/WebDAV.lean:169`); gate before every request (`Wasm/Ops/WebDAV.lean:471-483`); `gate_none`, `finish_unknown`, `finish_refused` (`Login.lean:399-416`) |
| failed-login limit (issue 1119, uncommitted) | `webdav/server.mjs` passes `remoteAddress` | `Login.lean` `Failures.check`, `loginKeys` | keys `name:` and `address:` (`loginKeys`); theorems `gate_limited`, `check_blocked`, `gate_no_derive_of_blocked`, `check_disabled` (uncommitted) |
| `xmpp-serve` | `npm/factoidal/xmpp/server.mjs` | `XMPP/Server.lean`, `Core.lean`, `Scram.lean` | server-stamped `from` (`#guard`, `XMPP/Server.lean:791-800`); RFC 6120 feature-order theorems (`Core.lean:150-168`); PLAIN and SCRAM-SHA-256 (`Server.lean:271`) |
| HTTP over XMPP, stage 1 | none yet | `XMPP/HttpOverXmpp.lean` (origin/main) | bare-JID allow list (`allowed` `:503`, checked first in `step` `:552`; `#guard`s `:667-670`); CONNECT refused; size limits `maxBodyBytes`, `maxPending` (`Config` `:432-443`) |
| `webdav-serve --xmpp`, step 1 (uncommitted) | host carries requests to `webdavStep` | `Wasm/Ops/XmppClient.lean`, `XMPP/ClientStream.lean` | SCRAM only, PLAIN refused; plain TCP accepted from the host (`ClientStream.lean` header items 1-2) |
| `factoidal serve` (SPARQL Protocol, Graph Store) | `npm/factoidal/bin/serve.mjs` | `SPARQL/StoreEndpoint.lean`, `SPARQL/Protocol.lean` | bound to 127.0.0.1 by default (`serve.mjs:359`); no authentication (not found) |
| SPARQL `SERVICE` | caller registers snapshots | `Wasm/Ops/ServiceReg.lean` | no network: an unregistered IRI is unreachable (module header) |
| SPARQL `LOAD` | none | `SPARQL/Update.lean:756` | no fetch: non-silent LOAD is an error |
| SPARQL extension functions | caller JavaScript callbacks | `Wasm/Ops/ExtFns.lean` | only registered IRIs reach the host; what the callback does is outside Lean |
| Synchronous HTTP reader (SBM11 over LWS) | `npm/factoidal/lib/sync-http-node.mjs` | `lib/sbm11-lws.mjs` | `redirect: 'follow'` (`sync-http-node.mjs:21`); no address guard (not found) |
| Network retrieval records | none | none | design only (`docs/designissues/2026-10-25-tabular-and-source-models.md` §4); issue 1035 open |
| Planned: native `httpx://`, raw LWS over XMPP, forwarding to third-party endpoints, MCP over XMPP | none | none | not found |

## 3. Combinations

Each row has an identifier (C1 to C13) and an invariant (I1 to I13). A
proposed theorem is written in Lean syntax. Names that do not exist yet
(`serveVia`, `Egress`, `peerOf`, ...) are proposals. Where the code cannot
carry a theorem yet, the check is a test that fails when the invariant breaks.
Per the owner's rule of 2026-09-07, an invariant that is not enforced gets an
expected-failure test and an open issue when this record lands. Section 6
lists the issues to open.

### C1. Local mounts (owner access) exposed over XMPP, with and without `--users`

Path. A local mount acts as the storage owner (`Wasm/Ops/WebDAV.lean:249`,
`insecureNoAuth`). Through HTTP over XMPP, a sender whose bare JID is in the
allow list sends PUT, DELETE, MOVE or PROPPATCH. On `origin/main`,
`HttpOverXmpp.serve` (`HttpOverXmpp.lean:534-541`) calls `WebDAV.handle`
directly. The login gate is not in `WebDAV.handle`: it is only in the wasm op
`webdavStepWith` (`Wasm/Ops/WebDAV.lean:471-483`). So a host that uses
`HttpOverXmpp.step` bypasses `--users`. Step 1 (uncommitted) sends each XMPP
request to `webdavStep` on the same handle, so `--users` applies there. Without
`--users`, every JID on the allow list owns every writable local mount, and the
WebDAV design record says "Every user reaches every mount"
(`docs/designissues/2026-10-27-webdav.md`, line 83).

Invariant I1. A request reaches a storage operation only when every access
check configured on the listener holds for it. The transport that carried the
request does not change this. The login check and the transport's own check
(allow list) both apply. Neither replaces the other.

Enforced today. The allow list: yes (`HttpOverXmpp.lean:552`, `#guard`s
`:667-670`, the end-to-end `forbidden` guard in `HttpOverXmppTests.lean`). The
login on the XMPP path: only by the host's routing in step 1, which is
uncommitted. No Lean function composes the two. Not enforced in Lean.

Proposed check. Move the login gate into one Lean entry that every transport
calls, and state `HttpOverXmpp.step` over it:

```lean
-- serveVia: the one entry; Principal is what the transport authenticated.
theorem serveVia_login_refused (cfg : ListenerCfg) (st : ListenerState)
    (p : Principal) (r : DavRequest) (h : cfg.login.isSome)
    (hr : (Login.gate H cfg.settings st.cache st.now (r.header? "authorization")).1 = .refuse) :
    ∃ st', serveVia cfg st p r = .pure (Login.unauthorized, st')
      ∧ st'.dav = st.dav

theorem plan_refuses_unallowed (cfg : HttpOverXmpp.Config) (st : State) (s : String)
    (env : Envelope) (rn : Node) (hreq : reqOf? s = some (env, rn))
    (h : HttpOverXmpp.allowed cfg.allow env.from_ = false) :
    plan cfg st s = .answer [renderRefusal env .forbidden] st
```

Test (expected failure until it holds): `webdav-serve CONFIGDIR --xmpp JID`
with a writable local mount, no `--users` and no explicit opt-in option, must
refuse to start. Today it would start (step 1).

### C2. Failed-login limit keyed by address; over XMPP there is no address

Path. The uncommitted limit counts each failure under `name:` + user name and
`address:` + `clientPrefix(remoteAddress)` (`loginKeys`, `clientPrefix`,
`Login.lean`, branch `rl-1119`). The wasm op reads `remoteAddress` with
default `""` (`Wasm/Ops/WebDAV.lean:494`, branch `rl-1119`). The step 1
request record that `xmppClientFeed` gives the host has `id`, `method`,
`target`, `headers` and `bodyBase64`, and no sender JID
(`Wasm/Ops/XmppClient.lean:130`, branch `xmpp-step1`). So every XMPP requester
shares the key `address:` (empty address):

- one allowed JID with 5 wrong passwords blocks the `address:` key for all
  XMPP requesters for 60 seconds (lockout of the other JIDs);
- the per-source limit is lost: one JID can try 5 passwords for each of many
  user names, and only the per-name key counts.

Also: `xmpp-serve` has no limit on failed SASL logins. No counter was found in
`XMPP/Server.lean` (`handleAuth`, line 393 onwards).

Invariant I2. Each failed login counts against a key that identifies the
requester on its transport: the client address (IPv4, or the IPv6 /64) on TCP,
the bare JID from the server-stamped `from` on XMPP. The key is never empty.
Keys of different transports never collide.

Enforced today. Not enforced (the limit is uncommitted, and has no JID key).

Proposed check.

```lean
inductive Requester | tcp (address : String) | xmpp (bareJid : String)

def requesterKey : Requester → String
  | .tcp a  => "address:" ++ clientPrefix a
  | .xmpp j => "jid:" ++ j

theorem requesterKey_injective_kind (a j : String) :
    requesterKey (.tcp a) ≠ requesterKey (.xmpp j)

theorem loginKeys_nonempty (u : String) (q : Requester) (hq : q ≠ .tcp "") :
    ∀ k ∈ loginKeys u q, k.length > "address:".length
```

Tests: (a) 6 wrong passwords from JID A, then the right password from JID B
for another name: B is not blocked. (b) 6 wrong passwords from JID A, each for
a different name: the 6th gets the refusal. (c) `xmpp-serve`: 6 failed SASL
attempts on one stream, or on new streams from one address, get
`temporary-auth-failure` or a closed stream (expected failure plus issue).

### C3. Where credentials go: `legacyChallenge`, `requireHttps`, subject tokens, `httpx`, WebDAV remote mounts

Paths.

1. Caller-given subject token. The client asks the first entry of
   `authorization_servers` in the protected resource metadata
   (`Machine.lean:1202-1204`). Checks 1 to 3 relate the metadata URL and the
   storage root to the requested URI. Nothing relates the authorization server
   to the requested URI or to a list that the caller trusts (not found). A
   self-issued credential has `aud` = that authorization server
   (`selfIssuedJwt`, `Machine.lean:1085-1091`), so another server cannot
   replay it. A subject token that the caller gave (`Session.subjectToken`, for
   example an OpenID Connect ID token) keeps the audience its issuer gave. A
   storage that names a hostile authorization server receives that token and
   can replay it at another authorization server that accepts the same
   provider and client.
2. `legacyChallenge`. `as_uri` is taken from the 401 with no check of its own
   (`Machine.lean:1169-1182`). The realm check is same origin plus string
   prefix (`legacyValidated`). Path 1 applies with fewer checks.
3. `requireHttps` off (the default, `Machine.lean:336`). Over `http`, a party
   on the network path writes the 401 and so chooses the authorization server
   and the storage root. Bearer tokens travel in clear text.
4. WebDAV remote mounts. `sessionOf` (`WebDAV/Remote.lean:129-147`) never sets
   `requireHttps`, and the mount `url` may be `http` (`Config.lean:177`,
   `:226`). A `bearer` mount sends the token file to `http` URLs.
5. Token scope. `TokenEntry.covers` is a string prefix (`Machine.lean:556-557`).
   A root without a final `/`, for example `https://s.example/alice`, covers
   `https://s.example/alice-other/`. Check 3 requires the same origin only.
   No path-segment boundary rule was found.
6. `anyToken` (a token with no realm) goes with every request, including a
   `next` page URL on another origin that the server chose (`Machine.lean:567`,
   `onPage` `:1054`).
7. `httpx`. `sameOrigin` is `false` for any URL that is not http or https
   (`LWS/Client/Wire.lean:92-95`), and `isHttpsUrl` requires `https://`
   (`Machine.lean:1668`). So today the token flow over `httpx` fails closed.
   The first `httpx` implementation must not relax this by a string rule.

Invariant I3. A credential goes only to a destination it is bound to:

- an access token: only to URLs under the root of the storage in its `aud`,
  with the same peer (scheme and authority for http and https; the
  authenticated JID for XMPP) and a path-segment boundary;
- a caller-given subject token: only to an authorization server that the
  caller named;
- a self-issued credential: `aud` = the authorization server it is sent to;
- a Basic password: only to the listener it was typed for, over TLS or
  loopback;
- with `requireHttps`, every request in every phase uses https or an XMPP
  stream with verified TLS.

Enforced today. `step_requireHttps` (`LWS/Client/Theorems.lean:211`): with the
option, every request uses https. `step_no_token_request_without_validation`
(`:243`): no token request without checks 1 to 3, or without the realm checks
in a session that turned on `legacyChallenge`. `attachToken_realm` (`:372`):
string prefix only. Not enforced: the authorization server choice, the segment
boundary, `requireHttps` for WebDAV mounts.

Proposed check.

```lean
def underRoot (root url : String) : Bool :=
  sameOrigin root url && pathSegmentsPrefix (pathOf root) (pathOf url)

theorem attachToken_dest (ses : Session) (r : Req) (t : String)
    (hany : ses.anyToken = "")
    (h : (attachToken ses r).header? "authorization" = some ("Bearer " ++ t))
    (hfresh : r.header? "authorization" = none) :
    ∃ e ∈ ses.tokens, e.token = t ∧ (underRoot e.root r.url ∨ ∃ x ∈ e.endpoints, underRoot x r.url)

-- New Session.trustedAs : List String; empty = no caller-given subject token is sent.
theorem step_subject_token_dest (V : Crypto) (s : ClientState) (e : Event) (r : Req)
    (h : (step V s e).2 = .fetch r) (hx : isTokenExchange r = true)
    (hsub : s.session.subjectToken ≠ "") (hsent : formField r "subject_token" = some s.session.subjectToken) :
    s.session.trustedAs.contains (issuerOfTokenEndpoint r.url) = true

theorem sessionOf_requireHttps (m : Mount) (C : Crypto) (k : Option ByteArray)
    (t : Option String) (ses : Session) (h : sessionOf m C k t = .ok ses)
    (hm : m.allowHttp = false) : ses.requireHttps = true
```

Tests: a mount file with `url: http://...` and `auth: bearer` is refused at
start unless it opts in; a storage description whose StorageRoot is
`https://s.example/alice` does not get the token for
`https://s.example/alice-other/x`.

### C4. JID allow list and the authenticity of `from`

Path. `allowed` trusts the `from` attribute (`HttpOverXmpp.lean:503`, `:552`).
That is correct only when (a) the XMPP server stamps `from` and (b) the stream
between that server and `webdav-serve --xmpp` is authenticated. For (a),
`xmpp-serve` stamps `from`, but only a `#guard` checks it
(`XMPP/Server.lean:791-800`). For (b), step 1 accepts plain TCP from the host
(`ClientStream.lean` header, items 1 and 2). On plain TCP a party on the
network path can insert `<iq type='set' from='alice@example.org/x'>` and get
owner access to local mounts (C1), and it can read Basic passwords and file
contents. `xmpp-serve` offers PLAIN also when `tlsCarrier` is false
(`Server.lean:167`, `:271`), so a listener bound to a non-loopback address
without `--cert` receives passwords in clear text. The WebDAV listener refuses
the same case for Basic (`Login.lean:220`, `Wasm/Ops/WebDAV.lean:169`).

Invariant I4. A transport that carries an identity used for an access decision
is authenticated end to end. For XMPP, the stream to the server uses TLS with
certificate verification, or the server is on loopback. A server offers a
password mechanism that sends the password (PLAIN) only on TLS or loopback.

Enforced today. HTTP Basic: yes (`transportAllowsBasic`). XMPP client stream:
not enforced. `xmpp-serve` PLAIN: not enforced. `from` stamping: `#guard` only.

Proposed check.

```lean
theorem clientOpen_refuses_plain (cfg : ClientStream.Config)
    (h1 : cfg.tls = false) (h2 : Login.isLoopback cfg.host = false) :
    (ClientStream.open cfg).isOk = false

theorem plain_offered_only_on_tls (cfg : Server.Config)
    (h : cfg.tlsCarrier = false) (hl : cfg.loopbackOnly = false) :
    "PLAIN" ∉ Server.mechanismsFor cfg

theorem route_from_stamped (s : Session) (env : Env) (u : Framing.Unit)
    (local_ res : String) (hb : s.stage = .bound local_ res) :
    ∀ o ∈ (step s env u).2.2, o.isRoute → o.fromJid = some (fullJid s.cfg local_ res)
```

### C5. Requests to private addresses: authorization server fetch, webhooks, access-request inboxes, SERVICE, forwarding

Paths.

1. Authorization server fetch. Guarded (`Fetch.lean:48`, `:121`,
   `chooseAddress_refuses_private` `:196`), and the address is pinned
   (`authz/server.mjs:126-141`). `privateAddr` (`Fetch.lean:48-55`) does not
   refuse 100.64.0.0/10 (shared address space, used by Tailscale, which
   `docs/web/hub/webdav.md` recommends for servers behind NAT),
   198.18.0.0/15, 192.0.0.0/24, 224.0.0.0/4, 240.0.0.0/4,
   255.255.255.255, fec0::/10, 64:ff9b::/96 (NAT64 with an embedded private
   IPv4 address), or 2002::/16 (6to4). Not found.
2. `lws-serve --authz --allow-private-fetch` turns the guard off for the
   mounted authorization server (`bin/factoidal.mjs:1977`). Any requester of a
   token can then make the server GET any internal URL (`sub` of a self-issued
   credential, OpenID Connect discovery).
3. Webhook inbox. Any http or https URL that is not this server
   (`Notifications.lean:956`, `:967`). Private addresses are accepted (not
   found). A name is resolved at subscription time only (`InboxGuard.lean`
   header, "A name resolved then is not resolved again at delivery time"). The
   host's `fetch` at delivery resolves it again (`lws/server.mjs:390`), so a
   name that resolves to a public address at subscription and to a private
   address at delivery passes (DNS rebinding). With `--insecure-no-auth`
   anyone can subscribe. With authorization, the subscriber must be able to read
   the topic (`Notifications.lean:1052`). The rate is per subscription
   (`admits_le`). Many subscriptions to one inbox multiply the deliveries to
   that inbox (not limited per destination: not found).
4. Access-request inbox. The only check is "not under `baseIri`"
   (`AccessGrants.lean:273-278`). No `InboxGuard.loops`, no private-address
   check (not found). A POST is sent when the controller creates a grant.
5. SPARQL `SERVICE`: no network (snapshots, `Wasm/Ops/ServiceReg.lean`). No
   host fetch hook for `SERVICE` was found in `npm/factoidal`. `LOAD`: no fetch
   (`SPARQL/Update.lean:756`). Extension functions: a caller's callback may
   fetch. That is outside every Lean guard (`Wasm/Ops/ExtFns.lean` header).
6. `lib/sync-http-node.mjs:21` follows redirects and has no address check. Its
   URLs come from the caller and from storage listings.
7. Forwarding to third-party endpoints over XMPP (planned): not found. Without
   an allow list, forwarding is an open proxy and a path into the local
   network.

Invariant I5. Each outbound request whose URL a remote party can choose
(subject `sub`, `jwks_uri`, webhook inbox, access-request inbox, redirect
`Location`, SERVICE IRI, forwarding target) passes one Lean decision. That
decision refuses every address in the IANA special-purpose registries unless
the operator opts in, and the host connects to the address the decision
chose. Deliveries to one destination are limited per destination, not only
per subscription.

Enforced today. Authorization server fetch: yes, with the gaps in path 1.
Webhooks, access-request inboxes, the sync reader: not enforced. Forwarding:
no code.

Proposed check. One module `L4Factoidal/Net/Egress.lean` (moved out of
`Authz/Fetch.lean`), used by `Authz.Fetch`, `Notifications`, `AccessGrants`
and every later fetching surface:

```lean
def specialPurpose : Addr → Bool   -- IANA IPv4 and IPv6 special-purpose registries

theorem egress_refuses_special (p : EgressPolicy) (host : String) (texts : List String)
    (a : Addr) (hp : p.allowPrivate = false) (ha : a ∈ texts.filterMap addr?)
    (hs : specialPurpose a = true) (x : String) : Egress.choose p host texts ≠ .ok x

theorem deliveries_pinned (cfg : Config) (st : State) (r : Request) :
    ∀ d ∈ (serverStep cfg st r).deliveries,
      ∃ texts, Egress.choose cfg.egress (hostOf d.url) texts = .ok d.address

theorem admit_per_destination (rate : Rate) (ns : NotifState) (now : Nat) (u : String) :
    (sentTo ns u now rate.window).length ≤ rate.destLimit
```

Tests (expected failures now): a webhook subscription with inbox
`http://10.0.0.1/` gets 400; an authorization server fetch of `100.64.0.1` is
refused; 20 subscriptions to one inbox give at most the per-destination limit
in one window.

### C6. Token audience with several transports

Facts. A storage has one audience, `storageIri` (`LWS/Authorization.lean:186`,
used at `:270`). The authorization server issues `aud` = exactly `[resource]`
(`issueToken_audience_exact`) for a configured resource
(`tokenRequest_resource`). The mounted authorization server has resources
`[storageIri]` (`Authz/Mount.lean`, `mountedOn`). The client does not run the
token flow over `httpx` (C3 path 7).

Path (when `httpx` or raw LWS over XMPP lands). (a) A storage is reachable at
`https://h/` and `httpx://dav@example.org/`. If the XMPP answer names the
https storage IRI, check 3 fails, and an implementer may relax check 3 to make
it pass. (b) If each transport gets its own storage IRI, and the server accepts
both audiences, a token for one storage on one host is accepted by another
storage. (c) A client token root `httpx://alice@example.org/` given as a
string prefix can cover URLs that name another resource of the same account,
or another account whose name starts with the same characters.

Invariant I6. One storage has one storage IRI, which is the audience. Every
transport that carries requests to that storage gives the same IRI in
`Link rel=".../lws#storage"` and in `resource_metadata`. A client sends a token
only over the transport peer from which it got that token: same scheme and
authority for http and https; same bare JID and resource for XMPP, with the
TLS of I4. A token is never sent to another JID.

Enforced today. The single audience: yes. Transport binding: no code yet. The
client fails closed (`sameOrigin`).

Proposed check.

```lean
inductive Peer | web (scheme authority : String) | xmpp (bareJid resource : String)

def peerOf? : String → Option Peer   -- http(s) and httpx URLs

theorem covers_same_peer (e : TokenEntry) (u : String) (h : e.covers u = true) :
    peerOf? u = peerOf? e.root ∧ (peerOf? u).isSome

theorem validateToken_aud_transport (cfg : Config) (a : AuthzConfig) (t : Transport) (tok : String) :
    acceptsVia t cfg a tok → (audOf tok).contains (storageIri cfg a)
```

### C7. Browser reach: CORS echo with `--insecure-no-auth`, DNS rebinding, cross-site form posts

Paths.

1. `lws-serve --insecure-no-auth` serves every request with no authorization
   (warning at `bin/factoidal.mjs:2039`). The CORS default answers any valid
   `Origin` (`corsConfig`, `bin/factoidal.mjs:1819-1827`; `LWS/Cors.lean`
   header). So any web page that the user opens can read and write the storage
   on 127.0.0.1 with `fetch()`. No credentials are necessary, so
   `Access-Control-Allow-Credentials` is not necessary either.
2. No listener checks `Host` (not found in `LWS/Binding.lean`,
   `LWS/Operations.lean`, `HTTP/Server.lean`, `WebDAV/Server.lean`; `WebDAV`
   reads `host` only for `If` tags and `Destination`, `Server.lean:571`,
   `:689`). A page on a domain that resolves first to the attacker and then to
   127.0.0.1 (DNS rebinding) is then same-origin with the listener. Without
   `--users`, `webdav-serve` local mounts give owner access to that page.
   `lws-serve --insecure-no-auth` and `factoidal serve` are in the same state.
3. `factoidal serve` accepts SPARQL Update as an
   `application/x-www-form-urlencoded` POST (`SPARQL/Protocol.lean:443`,
   `SPARQL/StoreEndpoint.lean:441`), with no authentication and no `Origin`
   check (not found). A form on any web site can POST `update=DROP ALL` to
   `http://127.0.0.1:3030/sparql`. This is a CORS simple request, so no
   preflight is sent.
4. CORS with credentials: the LWS profile never sends
   `Access-Control-Allow-Credentials` (`LWS/Cors.lean:77`, `#guard` `:147`;
   default `false`, `HTTP/Cors.lean:91`). A browser does not send cookies or
   cached Basic credentials in a way that lets a page read the answer. This
   holds today by a `#guard`, not by a theorem.

Invariant I7. A listener without authentication answers only requests whose
`Host` is a name or address it was bound to, or that is configured. It answers
no state-changing request whose `Origin` is another origin. CORS echo is never
the default when authorization is off. No CORS profile sends
`Access-Control-Allow-Credentials: true` together with echo.

Enforced today (https://github.com/danbri/factoidal/issues/1124, 2026-10-28).

* Paths 1 and 2, the `Host` check. `L4Factoidal/HTTP/LocalGuard.lean`:
  `admit g r` answers 421 Misdirected Request when `Host` names no name of
  the listener (theorem `localGuard_foreign_host`). The names: `localhost`,
  `127.0.0.1`, `[::1]`, the `--host` address, the addresses of the
  interfaces, the host of the base IRI (LWS, Solid), and `--allow-host NAME`
  (repeatable; a reverse proxy or Tailscale). The check is on the name only:
  a rebinding attack needs a name of the attacker. A request with no `Host`
  (no browser) is admitted.
* Path 3 and the writes of path 1, the `Origin` check. A method other than
  GET, HEAD and OPTIONS with an `Origin` that is not the listener's own
  origin (scheme http or https and `host[:port]` equal to `Host`) and not on
  the list (`--allow-origin ORIGIN`; for `lws-serve` also every
  `--cors-origin`) gets 403 (theorem `localGuard_cross_origin_write`). A
  request with no `Origin` is admitted (`localGuard_admits_no_origin`), and so
  is a safe method (`localGuard_admits_safe`). `factoidal serve`:
  `StoreEndpoint.handle` checks first; `handle_guard_refused` and
  `handle_cross_origin_update` prove that a refused request has no
  delta-log commit.
* Where the guard runs: `lws-serve --insecure-no-auth` and `solid-serve
  --insecure-no-auth` (`Wasm/Ops/Lws.lean` and `Wasm/Ops/Solid.lean`, before
  the CORS preflight and every other decision), `factoidal serve` (always; it
  has no authentication), and `webdav-serve` (always, also with `--users`,
  because a browser sends cached Basic credentials with a cross-site form
  POST; not on the `--xmpp` transport). Under authorization `lws-serve` and
  `solid-serve` do not run it, and `allowHosts` / `allowOrigins` (the
  options `--allow-host` / `--allow-origin`) are refused there.
* Path 1, the CORS default. With `insecureNoAuth`, a storage with no `cors`
  member sends no CORS field, and `cors: true` (echo) stops the start
  (`LWS.Cors.policyFor`, theorem `insecure_no_echo`). `lws-serve
  --insecure-no-auth` says why at start.
* Path 4. `HTTP.Cors.decorate_no_credentials` and
  `preflight?_no_credentials`: a profile with `credentials := false` adds no
  `Access-Control-Allow-Credentials`; `LWS.Cors.decorate_no_credentials`,
  `LWS.Cors.profile_no_credentials` and
  `Authz.corsProfile_no_credentials` instantiate them.

Not enforced, expected failures of
`npm/factoidal/test/local-guard-1124.test.mjs` under
https://github.com/danbri/factoidal/issues/1124:

* `solid-serve --insecure-no-auth` still echoes any `Origin` (Solid Protocol
  §8.1 requires the echo), so a page on another origin can READ the storage;
  writes from it get 403.
* The Solid profile (`Solid/Server/Cors.lean`) sends
  `Access-Control-Allow-Credentials: true` with the echo.

Tests: `npm/factoidal/test/local-guard-1124.test.mjs` (the three cases of
this record and the positive cases); `tests/lws/cors.mjs` check 20;
`tests/lws/cors-browser.mjs` checks 7 and 8 (Chromium: the page cannot read an
open storage, and a cross-site `no-cors` POST creates nothing).

### C8. Write tools over MCP (planned, issue 1121)

Path. No MCP code exists (`grep` for `jsonrpc` in `formal/lean4/L4Factoidal`
and `npm/factoidal/lib`: not found). When it lands, a tool call is made by a
model that can read untrusted content (a document fetched by another tool, a
notification body). Such content can ask for a write. The tool then writes with
the server's authority: owner access for a local mount (C1), the mount's
`did-key` or bearer token for a remote mount (C12), or the update endpoint of
`factoidal serve`. A read tool that fetches a URL is an outbound request (C5).

Invariant I8. A tool call acts with the authority of its caller (the JID of the
XMPP stanza under I4, or the bearer token of an HTTP call), never with more.
Each tool that writes is listed with its effect. A write tool needs a grant per
caller and per tool, and the default is to refuse. A tool that fetches uses
`Egress` (I5). A tool result never carries a credential (I10).

Enforced today. No code.

Proposed check.

```lean
theorem callTool_authority (cfg : McpConfig) (c : Caller) (t : Tool) (args : Json) :
    effectsOf (callTool cfg c t args) ⊆ permitted cfg c

theorem write_tool_default_deny (c : Caller) (t : Tool) (args : Json) (h : t.writes = true) :
    (callTool {} c t args).isRefusal = true
```

Test: a JID not in the grant list calls `lws.write`. The answer is a JSON-RPC
error, and the storage does not change.

### C9. Notifications sent as XMPP messages (planned, order item 4 of 2026-10-22)

Path. A subscriber names a JID as its inbox. If the JID can be any JID, the
server sends messages to accounts that did not ask for them, with change data
of resources. Every subscriber who can read one topic can direct its
notifications to a third party. The rate is per subscription only (C5 path 3).
If the server's XMPP account has a roster, the deliveries also change presence
traffic.

Invariant I9. An XMPP notification goes only to a JID bound to the
subscriber's authenticated identity: the subscription came over XMPP from that
bare JID (I4), or the JID answered a verification message. The per-destination
limit of I5 applies. `routed_authorized` (`Notifications.lean:775`) stays
true unchanged: only readers of a topic hear of it.

Enforced today. No code. `routed_authorized` covers the read check.

Proposed check.

```lean
theorem xmppDeliveries_bound (cfg : Config) (st : State) (r : Request) :
    ∀ d ∈ (serverStep cfg st r).xmppDeliveries, d.jid ∈ verifiedJids st d.sub.owner
```

### C10. Network retrieval records and credentials

Path. Issue 1035 is open and no record is written today. When it lands, a
record of an LWS client request holds the request headers (`Authorization:
Bearer ...`), the token exchange form (`subject_token=...`) and its JSON
answer (`access_token`). The WebDAV `bearer` mount, the `legacyChallenge`
flow and the authorization server's fetches all produce such records. The
CLAUDE.md rule removes credential header values and token query parameters,
but it does not name request and response BODIES of a token exchange.

Invariant I10. No retrieval record and no shared provenance subset holds a
credential value: `Authorization`, `Cookie`, `Set-Cookie`, token query
parameters, the `subject_token` and `actor_token` form fields, the
`access_token` and `refresh_token` members of a token answer, and Basic
passwords.

Enforced today. No code.

Proposed check: a test with a canary token. Run the LWS client token flow with
`subject_token` = `CANARY-1120`. No byte sequence `CANARY-1120`, and none of
its base64 or URL encodings, is in the record store or in the shared subset.
Theorem, when the record type exists:

```lean
theorem record_no_secret (req : Req) (resp : Resp) (s : String) (hs : s ∈ secretsOf req resp) :
    ¬ (s.isEmpty) → ¬ (renderRecord (recordOf req resp)).contains s
```

### C11. One directory served by `lws-serve` and `webdav-serve` at once

Path. The WebDAV design record says "do not serve one directory with
`lws-serve` and `webdav-serve` at once" (`docs/designissues/2026-10-27-webdav.md`,
line 62). Until 2026-10-28 nothing enforced it (no lock on the storage
directory was found in `webdav/server.mjs`, `lws/server.mjs`,
`lws/persist.mjs`); the lock below now does. Then the LWS
access policy of `lws-serve --authz` does not apply to WebDAV, or to XMPP
through `webdav-serve --xmpp`, because a local mount is the owner. Two writers
also overwrite each other's snapshot.

Invariant I11. A storage directory has one writing process. A local mount is
not exposed through a surface whose access check is weaker than that of the
storage's own server, unless the operator opts in.

Enforced today (2026-10-28, first part of I11): one writing process per
storage directory. `lws-serve DIR`, `solid-serve DIR` and every
`webdav-serve` local mount hold `DIR/lws.lock` while they run. A second
start on the same directory is refused with a message that names the lock
file and the holder (process id, command, start time, host). A lock whose
process does not run is taken over with a warning; a lock of another host is
refused. Lean decides (`L4Factoidal/LWS/DirLock.lean`, op `lwsDirLock`);
theorems `decide_alive_refuses`, `decide_otherHost_refuses`,
`decide_sameInstance_refuses`, `decide_replace_dead`, `decide_create_absent`.
Test: `node tests/lws/dir-lock.mjs` (a second `lws-serve`, `solid-serve` and
a `webdav-serve` local mount of a held directory are refused; a stale lock is
taken over with a warning; SIGINT and SIGTERM remove the lock). Issue:
https://github.com/danbri/factoidal/issues/1135.

Not enforced: the second part of I11. A local mount still answers through
WebDAV (and XMPP) as the storage's owner, so a directory served by
`webdav-serve` alone is not under the access policy that `lws-serve --authz`
would apply to it. A program that does not take the lock is not excluded.

### C12. Remote mounts with `did-key` or `bearer`, shared by many users and JIDs

Path. A remote mount holds one identity (`sessionOf`, `WebDAV/Remote.lean:129`).
Every `--users` user and every allowed JID reaches every mount (design record
line 83). So each of them acts as the mount's `did-key` identity at the remote
storage, with the access that the remote storage gave that identity. The
remote storage's access log names the mount's identity, not the person.

Invariant I12. A request through a mount acts for a principal that the mount
lists. A mount with credentials lists its principals (users and JIDs). An
empty list means the operator only.

Enforced today. Not enforced (the issue 1108 scope says that every user reaches
every mount).

Proposed check.

```lean
theorem handle_mount_principal (cfg : ListenerCfg) (st : ListenerState) (p : Principal)
    (r : DavRequest) (m : Mount) (hm : mountOf r = some m.name) (hp : p ∉ m.principals) :
    (serveVia cfg st p r).opsOf = []
```

### C13. Size and count limits shared between requesters

Path. `HttpOverXmpp.Config.maxPending` (16) and `maxBodyBytes` (16 MiB) are
limits for all senders together (`HttpOverXmpp.lean:432-443`). One allowed
JID that opens 16 chunked requests and never sends the last chunk blocks the
chunked uploads of every other JID. Waiting requests have no time limit (not
found). The same applies to the failed-login table (`maxKeys`, uncommitted):
it evicts no blocked counter, which is correct, but it refuses new keys when it
is full (`Failures.check`).

Invariant I13. A limit that protects the server is also kept per requester, so
one requester cannot use another requester's share. Waiting state has a time
limit.

Enforced today. Not enforced per requester.

Proposed check.

```lean
theorem plan_pending_per_sender (cfg : Config) (st : State) (s : String) :
    ∀ j, ((plan cfg st s).state.pending.filter (·.env.from_ == j)).length ≤ cfg.maxPendingPerSender
```

Test: JID A opens 16 chunked requests. JID B can still send one.

## 4. The five combinations with the highest risk

The order is by: present in the code today or about to land, default settings,
reach (any web page, any network peer), and effect (writes as the owner,
credential loss).

1. **C7: browser reach to listeners without authentication.** It was present
   with default settings until 2026-10-28: `lws-serve --insecure-no-auth`
   echoed any `Origin`, `factoidal serve` accepted a cross-site form POST of
   SPARQL Update, and no listener checked `Host`. The `Host` and `Origin`
   guard and the CORS default of row C7 close these paths; the Solid echo stays
   open under https://github.com/danbri/factoidal/issues/1124.
2. **C1 + C4: owner mounts over XMPP.** It is about to land (step 1).
   `HttpOverXmpp.step` on `main` bypasses `--users`. Without `--users`, every
   allowed JID is the owner. The allow list trusts `from` on a client stream
   that may be plain TCP. `xmpp-serve` offers PLAIN without TLS.
3. **C5: requests to private addresses.** It is present today. Webhook and
   access-request inboxes accept private addresses and resolve the name again
   at delivery. `privateAddr` does not refuse 100.64.0.0/10 (Tailscale) and
   other special-purpose ranges. Many subscriptions multiply the deliveries to
   one inbox. Forwarding (planned) would be an open proxy without an allow
   list.
4. **C3: where credentials go.** It is present today. A caller-given subject
   token goes to any authorization server that the storage names, with or
   without `legacyChallenge`. WebDAV `bearer` mounts send tokens over `http`.
   The token scope is a string prefix with no path-segment boundary.
5. **C2 + C13: limits keyed for one transport.** Over XMPP, the uncommitted
   failed-login limit falls back to an empty address key: one JID locks out
   the others, and the per-source limit is lost. `xmpp-serve` has no SASL
   failure limit. Waiting chunked requests are limited for all JIDs together.

## 5. Gate for a new surface

A PR that adds a surface (a server target, a transport, a client option, a
tool, an outbound fetch, a notification channel) states the items below in its
description and in its design record. If an answer is "none" or "not
enforced", the PR also adds an expected-failure test and an open issue for it
(owner rule of 2026-09-07).

1. **Kind.** Listener, transport, client option, tool, or outbound request.
2. **Principal.** Who is authenticated on this surface, by which Lean
   function, and how the transport makes that identity authentic (I4).
3. **Access decision.** The one Lean entry that every transport calls for this
   storage or endpoint (I1). Name the theorem that a refused request changes
   nothing (as `refused_keeps_state`).
4. **Credentials.** Each credential that the surface sends or receives, and the
   destinations it may go to (I3, I6). Default for TLS.
5. **Outbound requests.** Each URL a remote party can choose, and the `Egress`
   decision that it passes (I5).
6. **Browser reach.** CORS policy, the `Host` check, and simple requests that
   change state (I7).
7. **Limits.** Rate, size and count, each keyed per requester on this
   transport (I2, I13).
8. **Records.** What goes into retrieval or evidence records, and what is
   removed (I10).
9. **Rows.** The rows of section 3 that the PR adds or changes, with the
   invariants I1 to I13 it touches. For each invariant: a theorem name, or an
   expected-failure test plus its issue URL.
10. **Defaults and notice.** Off by default, a start-time warning for each
    unsafe option, and the review notice
    (`REVIEW_WARNING`, `bin/factoidal.mjs:96`).

A CI check can read item 9: each new `*serve*` command, transport op or
`Session` option in the diff must be named in a row of section 3. This record
is updated in the same landing (iron rule 14).

## 6. Issues

Opened when this record landed (2026-10-28), one per row of section 4:

- C7: https://github.com/danbri/factoidal/issues/1124
- C1 and C4: https://github.com/danbri/factoidal/issues/1125
- C5: https://github.com/danbri/factoidal/issues/1126
- C3: https://github.com/danbri/factoidal/issues/1127
- C2 and C13: https://github.com/danbri/factoidal/issues/1128

The expected-failure tests that name these issues are not in this landing.
Each issue lists its tests as work. The rows below have no issue yet and are
opened when their surface gets code. Each one gets an expected-failure test
that names it.

- I1, C1: one Lean listener entry with the login gate; `--xmpp` start rule.
- I2, C2: the requester key per transport; the `xmpp-serve` SASL failure limit.
- I3, C3: the authorization-server trust list for caller-given subject tokens;
  the path-segment rule for token scope; `requireHttps` for WebDAV mounts.
- I4, C4: TLS for the XMPP client stream; PLAIN only on TLS or loopback;
  `route_from_stamped` as a theorem.
- I5, C5: `Net/Egress.lean` (IANA special-purpose ranges, address pinning
  for deliveries, a per-destination limit); checks for access-request inboxes.
- I6, C6: one storage IRI across transports; `peerOf?` for `httpx`.
- I7, C7: landed 2026-10-28 under https://github.com/danbri/factoidal/issues/1124
  (`HTTP/LocalGuard.lean`, `LWS.Cors.policyFor`, `decorate_no_credentials`);
  the Solid echo and credentials remain, as expected failures under the same
  issue.
- I8, C8: authority and default deny for MCP tools (into issue 1121).
- I9, C9: JID verification for XMPP notifications.
- I10, C10: token exchange bodies in the redaction list (into issue 1035).
- I11, C11: a lock on the storage directory (landed 2026-10-28,
  https://github.com/danbri/factoidal/issues/1135); principals or an access
  check for local mounts.
- I12, C12: principals per mount.
- I13, C13: per-sender limits and a time limit for waiting chunked requests.

## 7. Surfaces added after this record

- 2026-10-28, `factoidal xmpp-http-proxy` (issue 1107 step 2): a listener
  (127.0.0.1 only) and an XMPP requester. Rows C1, C3, C4, C6 (no `httpx`
  token flow yet), C7, C13. The invariants, the theorems
  (`send_to_target`, `receive_to_target`, `tick_to_target`,
  `receiveNode_other_sender`, `forwardHeaders_sublist`,
  `forwardHeaders_keeps_authorization`) and the tests are in
  `docs/designissues/2026-10-28-http-over-xmpp.md`, "Step 2: invariants and
  their checks". Not met: the `Host`/`Origin` check of I7 on this listener,
  an expected failure that names https://github.com/danbri/factoidal/issues/1124.
