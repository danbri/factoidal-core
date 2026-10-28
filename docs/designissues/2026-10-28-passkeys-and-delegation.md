# Passkeys and delegated access for agents and companies (2026-10-28)

Tracking: https://github.com/danbri/factoidal/issues/1123 (passkeys and
delegation across LWS, Solid, WebDAV, XMPP and MCP). Related:
https://github.com/danbri/factoidal/issues/1120 (safety of feature
combinations).

Owner, 2026-10-28, verbatim: "Subagent looking at passkey use across this
protocol ecosystem- and issue/okr. Same issue - agent/company delegation eg
restricted access for eg GoogleTakeout but to write data in, or Gemini to
read/write, ditto other corporations and their tools, or independent, open
source etc tools and platforms. Review ietf work, Dick Hardt’s proposal aauth,
other oauth variants etc."

All sources were read on 2026-10-28 unless the text says otherwise. The code
statements refer to `danbri/factoidal-core` at commit `a7280741` (2026-10-28).
Decisions in this record are proposals by the coordinator's research agent.
The owner has not decided them.

## 1. Summary

1. A passkey proves one thing: at one moment, an authenticator that holds a
   private key for this relying party signed a challenge, and (with the UV
   flag) the authenticator checked a local user gesture or biometric. It does
   not prove who the person is, and it does not prove that the person read
   what the page showed. Section 2.4.
2. The narrowest safe use of a passkey here is to approve one access grant:
   the WebAuthn challenge is a digest of the grant document, and the grant
   record keeps the signed assertion as evidence. Section 2.5.
3. Factoidal can already express much of the delegation the owner asks for:
   an agent with its own controlled identifier (CID, https or did:key) gets a
   token from `authz-serve`, and the storage controller creates an LWS access
   grant that names that agent, the actions, the paths and a time window.
   Grants are checked on every request, so a revocation takes effect on the
   next request. Section 4.
4. Gaps in Factoidal: no WebAuthn code (0 Lean modules, 0 tests); no record
   of which grant permitted a request; a grant on a container does not reach
   its members (so "one area" is not expressible); LWS tokens are bearer
   tokens (DPoP exists only on the Solid path); `actor_token` is refused, so
   RFC 8693 delegation (`act`) is not available; no client authentication, so
   a grant's `client` constraint rests on a claim the client makes about
   itself. Section 5.
5. No standard today lets Google Takeout write into an LWS storage. Takeout
   writes only to Google Drive, Dropbox, Microsoft OneDrive and Box. Section 5.1.
6. The agent-authorization space is not settled. The IETF datatracker lists
   more than 200 Internet-Drafts from 2025-2026 with "agent" or "delegat" in
   the name. Of the OAuth WG documents, only identity chaining is in the RFC
   Editor queue. Dick Hardt's AAuth is an individual draft (revision 11). MCP
   authorization 2026-07-28 is stable enough to build on. Section 3.

## 2. Passkeys

### 2.1 Specifications and status

| Specification | Status | Source |
| --- | --- | --- |
| W3C Web Authentication Level 3 | W3C Recommendation, 25 August 2026; "no substantive changes" since the Candidate Recommendation Snapshot of 26 May 2026 | https://www.w3.org/TR/webauthn-3/ (version https://www.w3.org/TR/2026/REC-webauthn-3-20260825/) |
| FIDO Client to Authenticator Protocol (CTAP) 2.3 | FIDO Proposed Standard, 26 February 2026 | https://fidoalliance.org/specs/fido-v2.3-ps-20260226/fido-client-to-authenticator-protocol-v2.3-ps-20260226.html |
| CTAP 2.2 | FIDO Proposed Standard, 14 July 2025 (URL date) | https://fidoalliance.org/specs/fido-v2.2-ps-20250714/fido-client-to-authenticator-protocol-v2.2-ps-20250714.html (not opened; listed by search) |
| W3C Secure Payment Confirmation | Candidate Recommendation Draft, 13 October 2026 | https://www.w3.org/TR/secure-payment-confirmation/ |

What WebAuthn Level 3 contains that matters here (section numbers of the
Recommendation):

- Credential backup state: the authenticator data flags carry backup
  eligibility (BE) and backup state (BS) (§6.1.3). A relying party can see
  whether a credential can be synced ("synced passkey") or is bound to one
  device. It cannot see where it is synced to.
- Attestation: `attestation` defaults to `"none"` in
  `PublicKeyCredentialCreationOptions` (IDL in §5.4). With "none" the client
  replaces "potentially uniquely identifying information with non-identifying
  versions". Attestation formats in §8; conveyance preference in §5.4.7.
- Conditional mediation: `mediation: "conditional"` for get and create, and
  `isConditionalMediationAvailable()`. The user agent shows passkeys in the
  autofill list of an input with the `webauthn` autofill token.
- Related origins (§5.11) with the well-known URI `/.well-known/webauthn`
  (§12.5): one RP ID can be used from a listed set of other origins.
- `getClientCapabilities()` (§5.1.7) and the signal methods
  `signalUnknownCredential`, `signalAllAcceptedCredentials`,
  `signalCurrentUserDetails` (§5.1.10): the relying party tells the passkey
  provider which credentials are gone.
- Test vectors (§16): 15 sets (§16.2 to §16.16): attestation "none" with
  ES256 (also cross-origin, top-origin and long credential ID), packed
  (self, ES256, ES384, ES512, RS256, EdDSA, Ed448), TPM, Android Key, Apple,
  FIDO U2F.

CTAP 2.3 §11.5 defines "hybrid transports": a phone acts as the
authenticator for another device, started by a QR code (§11.5.1) or by
stored state (§11.5.2). The search summary of the Yubico page
(https://developers.yubico.com/CTAP/CTAP2.3.html, not opened) says CTAP 2.3
adds Bluetooth Low Energy as a data channel for hybrid and has no breaking
changes from 2.2. I did not verify this in the specification text.

FIDO defines a passkey as "an authentication credential based on FIDO
standards"; "Passkeys can be securely synced across a user's devices";
device-bound passkeys "never leave a single device"
(https://fidoalliance.org/passkeys/). The page does not describe the
Credential Exchange Protocol; I did not review it.

### 2.2 Passkeys for clients that are not browsers

- Native applications use the platform passkey APIs (Apple Authentication
  Services, Android Credential Manager). These bind an application to an RP
  ID through an association file on the domain. I did not read the Apple or
  Android documentation for this record; treat this point as unverified.
- A command-line tool can talk CTAP directly to a USB or NFC security key
  (device-bound credential). A synced passkey in a platform passkey manager
  is reachable only through the platform API or a browser.
- An agent process cannot use a passkey by itself: user verification needs a
  local gesture at the authenticator. The usual pattern is a device flow:
  the tool shows a code, the person signs in with a passkey in a browser on
  any device, and the tool gets a token. RFC 8628 (OAuth 2.0 Device
  Authorization Grant, August 2019) defines it. RFC 10027 ("Cross-Device
  Flows: Security Best Current Practice", published from
  draft-ietf-oauth-cross-device-security-16; datatracker state "RFC
  Published") lists the phishing risks of this pattern
  (https://datatracker.ietf.org/doc/draft-ietf-oauth-cross-device-security/).
- draft-ietf-oauth-first-party-apps-04 (26 August 2026; state "WG
  Consensus: Waiting for Write-Up") defines an Authorization Challenge
  Endpoint for a "browserless" first-party login. Its Appendix A.1 shows a
  passkey challenge
  (https://www.ietf.org/archive/id/draft-ietf-oauth-first-party-apps-04.txt).
  It is for first-party applications only.

### 2.3 Passkeys and each Factoidal protocol

| Surface | Today in Factoidal | Passkey route found | Status of that route |
| --- | --- | --- | --- |
| OAuth / OIDC (`authz-serve`) | Token exchange only (RFC 8693) with subject tokens: OIDC ID token, CID (https, did:key), SAML. No login page. | The authorization server (or an OpenID provider) logs the person in with WebAuthn, then issues tokens. WebAuthn is an authentication method of the AS; OAuth does not define it. | Standards exist (WebAuthn REC, OAuth). Nothing in Factoidal. |
| LWS (`lws-serve`) | Bearer tokens from a trusted AS; no own login. | Through the AS. LWS 1.0 core (Working Draft, 23 October 2026, https://www.w3.org/TR/lws10-core/) defines authentication suites as token types (§4.3); a passkey is not a token type. | No LWS text on passkeys. |
| Solid | Solid-OIDC with DPoP (`Solid/Server/Auth.lean`). | Through the OpenID provider. | Solid-OIDC v0.1.0 (https://solidproject.org/TR/). |
| XMPP (`xmpp-serve`) | SASL PLAIN and SCRAM-SHA-256 (`XMPP/Server.lean`). | draft-bucksch-sasl-passkey-00 (4 August 2025, individual, "SASL Passkey"). I found no later revision; an Internet-Draft expires after six months. It says the passkey is created "via other means" (on the web site) and the client passes the challenge "as-is to the OS authenticator API". I found no text on how the WebAuthn origin and RP ID are set for a non-web client. https://www.ietf.org/archive/id/draft-bucksch-sasl-passkey-00.txt | Not a basis for implementation. |
| XMPP fast reconnect | none | XEP-0388 Extensible SASL Profile (SASL2), 1.0.4, 2025-08-25, status "Draft" in the XML source and "Stable" on the rendered page; XEP-0484 Fast Authentication Streamlining Tokens (FAST), 0.2.0, 2024-06-30, "Proposed"; FAST uses the HT-* mechanisms of draft-ietf-kitten-sasl-ht-02 (2026-06-25). XEP-0440 SASL Channel-Binding Type Capability, 1.0.0, 2025-12-08, "Stable". https://xmpp.org/extensions/xep-0388.html, https://xmpp.org/extensions/xep-0484.html, https://xmpp.org/extensions/xep-0440.html | A login done once with a passkey (web) can give a FAST token for later SASL logins. This is a pattern, not a specification. |
| XMPP third-party access | none | XEP-0493 OAuth Client Login, 0.1.1, 2025-03-31, "Experimental" (https://xmpp.org/extensions/xep-0493.html). | Early. |
| WebDAV (`webdav-serve --users`) | HTTP Basic, PBKDF2-HMAC-SHA256, 600,000 iterations; no limit on failed logins (https://github.com/danbri/factoidal/issues/1119). | None found. RFC 4918 has no authentication scheme of its own. A passkey can protect the page where a person makes a per-client password or token for a WebDAV client. | No standard. |
| MCP | planned over XMPP (`docs/designissues/2026-10-28-mcp-over-xmpp.md`) | Through the AS of the MCP server (OAuth 2.1). | MCP 2026-07-28. |

### 2.4 What a passkey proves, and what it does not

From WebAuthn Level 3: user verification "does not give the Relying Party a
concrete identification of the user"; repeated user verification with one
credential "expresses that it was the same user that performed all of them";
a user presence test "does not constitute user verification".

So a verified assertion says:

- The holder of credential C, registered for RP ID R, signed challenge X.
- With UV = 1: the authenticator did a local check (PIN, biometric).
- With BS = 1: the key can exist on other devices of the same passkey
  provider account. A person who controls that account (or an attacker who
  takes it over) can use the key from any of them.
- The origin and, for cross-origin calls, the top origin are in
  `clientDataJSON`, which the browser writes.

It does not say:

- which person it is (only that it is the same as at registration);
- that the person read or understood the grant that the page showed (the
  authenticator shows only the RP ID and account name, never the grant);
- that the software that asked for the assertion is honest (a compromised
  page or extension can ask for an assertion over a different challenge).

Secure Payment Confirmation is the only W3C mechanism found in which the
browser itself shows the data that the signature covers (payment details go
into `clientDataJSON`). It is for payments. I found no general WebAuthn
transaction-confirmation extension in Level 3.

### 2.5 Binding a passkey to a delegated grant

Proposed binding (no specification defines it; it uses only WebAuthn as
specified):

1. The person opens the grant page of the authorization server or storage.
   The server makes the grant document G (LWS access grant JSON) and its
   canonical bytes (RFC 8785 JSON Canonicalization Scheme).
2. Challenge X = SHA-256( "lws-grant-v1" ‖ canonical(G) ‖ server nonce N ).
   N is single-use, with a short lifetime.
3. The page calls `navigator.credentials.get` with challenge X and
   `userVerification: "required"`.
4. The server verifies the assertion (RP ID hash, origin, UV, signature,
   signature counter where not zero) and recomputes X from G and N. Only
   then does it store G.
5. The grant record keeps: credential ID, `authenticatorData`,
   `clientDataJSON`, signature, N, the flags (UV, BE, BS), and the time.
   Anyone with the public key can check later that this credential approved
   these exact grant bytes.

What this gives: a grant cannot be created or widened by a stolen session
cookie or token alone; each grant has signed evidence. What it does not give:
proof that the person read G (Section 2.4).

## 3. Delegation: specifications and status

### 3.1 IETF OAuth

| Document | Status (datatracker, 2026-10-28) | What it gives here |
| --- | --- | --- |
| RFC 8693 OAuth 2.0 Token Exchange | RFC, January 2020 | §1.1: with impersonation "A is given all the rights that B has"; with delegation "principal A still has its own identity separate from B". §4.1 `act`: "The outermost act claim represents the current actor while nested act claims represent prior actors"; prior actors are "informational only" for access control. §4.4 `may_act`: who may become the actor. https://www.rfc-editor.org/rfc/rfc8693.html |
| RFC 9396 Rich Authorization Requests | RFC, May 2023 | `authorization_details`: typed JSON (actions, locations, datatypes). Fits an LWS grant shape. |
| RFC 9449 DPoP | RFC, September 2023 | Sender-constrained tokens (`cnf.jkt`). |
| RFC 8707 Resource Indicators | RFC, February 2020 | `resource` parameter; audience of the token. |
| RFC 9728 Protected Resource Metadata | RFC, April 2025 | Discovery from the resource. |
| RFC 9635 GNAP; RFC 9767 GNAP Resource Server Connections | RFC, October 2024; RFC, April 2025 (https://www.rfc-editor.org/rfc/rfc9767) | A separate protocol with rich access requests and interaction. No deployment base found in agent products. |
| draft-ietf-oauth-v2-1-16 | WG Document, 2026-09-03 | OAuth 2.1; MCP cites revision 13. |
| draft-ietf-oauth-identity-chaining-17 | In RFC Editor queue ("RFC Ed Queue"), 2026-08-21 | "A JSON Web Token (JWT) authorization grant, obtained through an intra-domain OAuth 2.0 Token Exchange, facilitates the cross-domain acquisition of an access token." |
| draft-ietf-oauth-transaction-tokens-11 | "WG Consensus: Waiting for Write-Up", 2026-08-21 | Context for a call chain "within a trusted domain". Not for cross-domain use. |
| draft-ietf-oauth-client-id-metadata-document-02 | WG Document, 2026-07-06 | A URL as `client_id`; the AS fetches the client's metadata. MCP's preferred registration. |
| draft-ietf-oauth-identity-assertion-authz-grant-04 | WG Document, 2026-05-21 | "Cross-App Access": an enterprise IdP issues a grant for a third-party API. |
| draft-ietf-oauth-status-list-21 | In RFC Editor queue, 2026-08-13 | Token status (revocation) lists. |
| draft-ietf-wimse-aims-00 | WIMSE WG document, 2026-09-15, Informational | "Rather than defining new protocols, this document describes how existing and widely deployed standards can be applied" to AI agents. Replaces draft-klrc-aiagent-auth. https://www.ietf.org/archive/id/draft-ietf-wimse-aims-00.txt |

Sources: https://datatracker.ietf.org/api/v1/doc/document/ (queried per
document) and the archive texts under https://www.ietf.org/archive/id/.

Individual drafts on agents. A datatracker query (names containing "agent",
"delegat", "on-behalf", "aauth"; changed since 2025-01-01) returned more than
200 drafts. Examples with OAuth in the name: draft-hamr-oauth-agent-delegation-03,
draft-mishra-oauth-agent-grants-02, draft-niyikiza-oauth-attenuating-agent-tokens-02,
draft-chen-oauth-agent-authz-use-cases-05, draft-mcguinness-oauth-ai-agent-instance-00,
draft-oauth-transaction-tokens-for-agents-06; and
draft-oauth-ai-agents-on-behalf-of-user-02 (expired). None is a WG
document. I did not read them; the count shows that there is no agreed
design yet.

### 3.2 AAuth (Dick Hardt)

Primary source: draft-hardt-oauth-aauth-protocol-11, 25 September 2026,
individual Internet-Draft, Standards Track intended, datatracker state
"Active, I-D Exists" (not adopted by a WG). Repository:
https://github.com/dickhardt/AAuth. Text:
https://www.ietf.org/archive/id/draft-hardt-oauth-aauth-protocol-11.txt. It
replaces draft-hardt-aauth-protocol-02 (28 April 2026). Companion drafts:
draft-hardt-httpbis-signature-key-09, draft-hardt-aauth-r3-00 (rich resource
requests), -events-00, -budgets-00, -bootstrap-02, -headers-00 (all
September and October 2026).

Name clash: draft-rosenberg-oauth-aauth-01 ("AAuth - Agentic Authorization
OAuth 2.1 Extension", April 2026, expired) and draft-patwhite-aauth-00 (May
2025) are different proposals with the same name.

Model (from -11):

- Agent identity: "every agent has its own cryptographic identity. An agent
  identifier (aauth:local@domain) is bound to a signing key, published at a
  well-known URL". An agent provider issues an agent token that binds the
  identifier to the key.
- No bearer tokens: every request is signed with HTTP Message Signatures
  (RFC 9421); "no credential is a bearer credential, and none needs
  pre-registration, so the first API call to a resource is the
  registration".
- Five access modes: agent identity; resource-managed (two-party); person
  identity; person server (PS) authorization (three-party); federated
  (four-party, PS with an access server, AS).
- Person server: "asserting who the agent acts for, managing consent and
  missions, relaying interactions and payments, and recording what the agent
  did". It has permission, audit and interaction endpoints (§7.7 to §7.8).
- Missions (§8): "a Markdown description of what the agent intends to
  accomplish, proposed by the agent and approved by the person"; its hash
  `mission_s256` goes into later tokens.
- Auth token (§9.4.1): `cnf` binds it to the agent key; lifetime at most one
  hour and never after the agent token, the presented token or the mission;
  `sub` is a pairwise identifier per resource; it "carries no agent
  identifier and no delegation chain".
- Call chaining (§10.1.1): an intermediary acts as an agent with its own key
  and presents the caller's token as `upstream_token`; downstream access
  "does not outlive it". Sub-agents: single-level depth (§10.2.2).

Assessment: AAuth addresses the owner's cases directly (agent identity,
person consent, audit, short sender-bound tokens). It is one author's draft
at revision 11 with a fast rate of change; no WG has adopted it. Its
agent-identity mode (signed request, decision by agent identifier) is close
to what Factoidal has with CID subjects and LWS grants.

### 3.3 W3C, OpenID and other work

- LWS 1.0 core, W3C Working Draft 23 October 2026
  (https://www.w3.org/TR/2026/WD-lws10-core-20261023/). §11 Access Requests
  and Grants: "An agent does not present an access grant to a server as an
  authorization token." Grants have actions read, modify, create, delete;
  an `assignee` URI; constraints `client`, `format`, `type`, `purpose`,
  `dateTime`. Revocation is `DELETE` of the grant. §16.2 mentions audience
  binding and DPoP as protections (non-normative). §16.4: servers are
  "encouraged to verify that the assignee value in the request" matches the
  authenticated agent. I found no text on `act`, `may_act` or delegation
  chains. The fetch read the first 200,000 of 217,695 characters.
- Solid (https://solidproject.org/TR/, page modified 2026-10-17): Solid
  Protocol CG-DRAFT v0.11.0; Solid-OIDC v0.1.0; Web Access Control CG-DRAFT
  v1.0.0; Access Control Policy v0.9.0; Solid Application Interoperability
  CG-DRAFT v0.1.0. No report on that page is titled "access grants".
- Verifiable Credentials Data Model 2.0: W3C Recommendation, 15 May 2025
  (https://www.w3.org/TR/vc-data-model-2.0/). It notes that "A holder is
  often, but not always, a subject"; the part I read defines no normative
  delegation mechanism.
- ZCAP (Authorization Capabilities), W3C CCG, latest listed version v0.4.0
  (https://w3c-ccg.github.io/zcap-spec/); the index page gives no status
  sentence or date.
- UCAN 1.0.0 (https://github.com/ucan-wg/spec): "Each direct delegation MUST
  either directly restate or attenuate (diminish) its capabilities". The
  page gives no date or formal status.
- UMA 2.0 Grant for OAuth 2.0: Kantara Recommendation, 2018-01-07
  (https://docs.kantarainitiative.org/uma/wg/rec-oauth-uma-grant-2.0.html).
  The owner sets policy ahead of time; the client gets a permission ticket
  at the resource and redeems it at the AS.
- OpenID Foundation: whitepaper "Identity Management for Agentic AI", AI
  Identity Management Community Group, arXiv:2510.25819 (29 October 2025);
  announcement https://openid.net/new-whitepaper-tackles-ai-agent-identity-challenges/.
  I read only search summaries, not the paper. "OIDC-A 1.0" is a paper by
  one author (arXiv:2509.25974, 30 September 2025), not an OpenID
  Foundation specification. draft-sharif-openid-agent-identity-02 is an
  individual IETF draft.
- MCP authorization, revision 2026-07-28
  (https://modelcontextprotocol.io/specification/2026-07-28/basic/authorization):
  the MCP server is an OAuth 2.1 resource server; it "MUST implement" RFC
  9728; clients "MUST implement" RFC 8707 and send `resource` on both
  requests; Client ID Metadata Documents SHOULD be supported and Dynamic
  Client Registration "is deprecated"; servers "MUST validate that access
  tokens were issued specifically for them as the intended audience"; "MCP
  servers MUST NOT accept or transit any other tokens". The page does not
  mention RFC 8693 or DPoP. Authorization is for HTTP transports; other
  transports "MUST follow established security best practices for their
  protocol".
- Gemini CLI (one client of the owner's case b): "Perform dynamic client
  registration if supported", needs a local browser, does not mention Client
  ID Metadata Documents or RFC 8707
  (https://geminicli.com/docs/tools/mcp-server/). I did not find a public
  document on how the consumer Gemini app connects to third-party storage.

## 4. What Factoidal has today

All in Lean, under `formal/lean4/L4Factoidal/`:

- `Authz/Server.lean`: RFC 8414 metadata, JWK Set, RFC 8693 token exchange.
  Access tokens (RFC 9068) carry `iss`, `sub`, `aud` = exactly the one
  resource, `client_id`, `iat`, `exp` (lifetime at most 300 s), `jti`.
  `actor_token` is refused: "actor_token (delegation) is not supported".
- `Authz/SubjectToken.lean`: subject suites. In the CID suite "The claims
  sub, iss, and client_id MUST all use the same URI value"; so a
  self-issued agent is both subject and client. In the OIDC suite the client
  is the ID token's `azp`.
- `LWS/AccessPolicy.lean`, `LWS/AccessGrants.lean`: grants are part of the
  access policy. `Authorization.decide` consults `grantAllows` beside Web
  Access Control on every request. Theorems: `grantsPermit_sound` (a grant
  permits only what it lists), `grantsPermit_revoke` (a deleted grant
  permits nothing), `recordPermits_expired`, `policyPermits_excluded`,
  `accessStep_grant_needs_controller` (only the controller creates grants).
  Server choices: "A grant on a container does not reach its members"; a
  `purpose` constraint permits nothing; a grant never reaches an ACL
  resource. 102 `#guard`s in `LWS/AccessGrantsTests.lean`.
- `JOSE/DPoP.lean`: RFC 9449 proof checks, used by the Solid server only.
  `LWS/Authorization.lean`: "The draft names no DPoP binding; Bearer is the
  only scheme."
- Measured: `node tests/authz/server.mjs` gives 48 pass, 0 fail, 0 xfail,
  0 skipped (out of 48), with the wasm installed in this checkout (stamp not
  checked against this commit).
- Not present: WebAuthn or passkeys (0 files match `webauthn|passkey` under
  `formal/lean4` and `npm/factoidal`); CBOR (needed for WebAuthn attestation
  objects and COSE keys); a record of which grant permitted a request
  (`grantAllows` returns `Bool`); client authentication at the token
  endpoint.

## 5. Worked cases

Common model (proposal): each tool has its own identifier (CID URL or
did:key; later a Client ID Metadata Document URL). The storage controller
signs in with a passkey and approves an LWS access grant (Section 2.5) that
names the tool as `assignee`. The tool gets a short access token for the
storage from `authz-serve` with its own subject token. The storage checks the
grant on every request. Revocation is `DELETE` of the grant.

### 5.1 Google Takeout writes into one container, once or for a period

- Today: Takeout delivery methods are a download link, "Add to Drive", "Add
  to Dropbox", "Add to Microsoft OneDrive", "Add to Box". For Dropbox the
  user allows "Google Download Your Data" to access "its own 'Apps' folder".
  Scheduled export: "every 2 months for one year"
  (https://support.google.com/accounts/answer/3024190?hl=en). I found no
  Takeout interface for other destinations.
- Flow if Google adopted LWS: person signs in with a passkey; approves grant
  {assignee: Takeout's agent identifier; action: create; target: Container
  `/imports/google/`; dateTime gteq now, lteq now + 1 year}. Takeout gets a
  token (aud = the storage, 300 s) and POSTs archives into the container.
- Enforcement: `create` in that container only. Takeout cannot read, modify
  or delete, also not its own uploads (each is a new resource; `modify` is
  checked on the member path). "Once" is not expressible: LWS constraints
  have no count. A narrow `dateTime` window is the closest.
- Revocation: `DELETE` the grant; the next POST fails.
- Audit: today the journal records the write; no record names the grant.
- Specs that support it today: LWS grants (WD), RFC 8693, RFC 8707. Blocking
  fact: Google does not offer this; no standard makes it offer it.
- Factoidal has: grants, windows, create-only. Lacks: passkey-approved
  grant, grant-use record, count constraint, an agent identifier type that a
  large provider would use (Google's OIDC `sub` is not a URI whose document
  names Google as `lws#OpenIdProvider`, so the LWS OIDC suite does not
  apply).

### 5.2 Gemini or another assistant reads and writes one area, revocably

- Flow: the assistant connects as an MCP client to an MCP server in front of
  the storage, or directly as an LWS client. Person approves grant
  {assignee: the assistant's identifier; actions read, modify, create,
  delete; target: the area; client: the assistant's client ID}.
- Gap 1: "one area" needs every resource under a container. Factoidal's
  grants do not reach members. Options: (a) the grant lists each path (does
  not cover new resources); (b) a server extension "container and members",
  off by default, recorded as an extension and raised with the LWS WG; (c)
  Web Access Control `acl:default` on the container for the agent (exists
  today, but it is not a recorded, time-limited grant).
- Gap 2: the MCP path. MCP forbids token passthrough. So the MCP server needs
  its own LWS token for the person. With RFC 8693: the MCP server presents
  the person's subject token and its own actor token; the issued token has
  `sub` = person, `act.sub` = MCP server. Factoidal refuses `actor_token`
  today.
- Revocation: `DELETE` the grant (immediate at the storage); tokens expire
  within 300 s.
- Audit: should show assistant identifier, client, grant ID, action, path,
  time; and, on the MCP path, the person and the actor.
- Specs: LWS grants, RFC 8693 (`act`, `may_act`), MCP 2026-07-28, RFC 9449.

### 5.3 Other companies' tools

As 5.2. In an enterprise, the company's IdP can issue the grant across
applications (draft-ietf-oauth-identity-assertion-authz-grant-04, Cross-App
Access) or across domains (identity chaining, RFC Editor queue). Factoidal
lacks both. A `client` constraint is only as strong as client
identification: the CID suite has `client_id` = `sub` (the tool is the
subject), so it holds when the tool has its own CID; in the OIDC suite it is
the OP's `azp`.

### 5.4 Independent and open-source tools

- A tool on the person's own machine (CLI, local agent): device flow (RFC
  8628) or a self-issued did:key subject token. The person approves the grant
  with a passkey in a browser.
- A tool with no web origin cannot be an RP itself. It holds its own key
  (did:key); the grant names that key's identifier.
- Risk: the key file on disk is the authority. A short window and a narrow
  target limit the loss.

## 6. Risks and the invariants for issue 1120

Each line is an entry proposed for https://github.com/danbri/factoidal/issues/1120.

1. Confused deputy. An MCP server or proxy with broad access does what a
   less-privileged caller asks. Invariant: the storage sees the caller's own
   authority or a narrower one, never the deputy's
   (`docs/designissues/2026-10-28-mcp-over-xmpp.md` states the same).
   Enforce: the deputy gets a token whose `sub` is the caller and whose grant
   check runs for that `sub`.
2. Token passthrough. Invariant: a token is accepted only with `aud` equal
   to this resource, and a server never sends a received token onward. MCP
   2026-07-28 makes this a MUST. Theorem target: no outbound request of a
   host step carries an `Authorization` value from an inbound request.
3. Over-broad scope. Invariant: a grant permits only what it lists
   (`grantsPermit_sound`, exists). Any new "members" matcher must keep a
   theorem of the same form.
4. Agent impersonation. With impersonation semantics (RFC 8693 §1.1) the
   storage cannot tell the agent from the person. Invariant: every token
   issued for an agent names the agent (as `sub` with a grant, or as
   `act.sub`); no exchange path issues a person-`sub` token to an agent with
   no `act`.
5. Consent fatigue. Many prompts make people approve without reading. Use
   few, durable grants with narrow targets and windows; one passkey
   assertion per grant, not per request.
6. Revocation lag. Grants are checked per request (no lag at the storage).
   Tokens live at most 300 s. A cached grant list in another process, or a
   token for another resource server, can lag. Invariant: revocation is
   effective at the next request to the storage (`grantsPermit_revoke`).
7. Cross-domain identity chaining. Each domain boundary adds a trust
   assumption. Defer until identity chaining is an RFC.
8. Prompt injection steers an agent to use a grant for another purpose. No
   protocol stops this. Limits: narrow grants, write-only where possible,
   per-grant audit, an anomaly report to the controller. `purpose` is not
   enforceable (the draft says no way to state it).
9. Synced passkey account takeover. A BS = 1 credential is as strong as the
   passkey provider account. Option: require BE = 0 (device-bound) for the
   controller credential that approves grants.
10. Login rate limits on new paths. Over XMPP there is no client address
    (https://github.com/danbri/factoidal/issues/1119); passkey and token
    endpoints need limits keyed by account and transport identity.

## 7. Recommended order (fastest and safest first)

1. Grant-use record (Lean, small). `grantAllows` returns the ID of a grant
   that permits; `Authorization.decide` puts it in the decision; the host
   appends a journal line {time, agent, client, grant ID, action, path,
   status}. Theorem: if the decision cites grant g, then g permits the
   request. No new crypto, no new protocol.
2. Issue 1120 entries for invariants 1-4 and 6, each with a test that fails
   when the invariant breaks (Section 6).
3. DPoP on the LWS path (Lean: reuse `JOSE/DPoP.lean`; AS puts `cnf.jkt` in
   tokens when the request has a DPoP proof; storage checks it). Off by
   default, because the LWS draft names Bearer only.
4. WebAuthn relying party in Lean: parse `authenticatorData` and
   `clientDataJSON`; verify ES256 (HACL\* P-256, exists), EdDSA (exists),
   RS256 (exists); attestation "none" only; a minimal CBOR subset for the
   attestation object and COSE key. Test with WebAuthn §16.2 to §16.6.
   The host gives bytes and does no checks.
5. Passkey login and passkey-approved grants in `authz-serve` (Lean decides;
   host serves the page and calls `navigator.credentials`). Section 2.5
   binding. The controller credential may require BE = 0.
6. RFC 8693 `actor_token` with `act` and `may_act`, for the MCP server and
   other deputies. Theorem: an issued token with an actor names it in
   `act`; prior actors do not change the decision.
7. "Container and members" grant target as an opt-in extension, with a
   soundness theorem; raise it with the LWS WG.
8. XMPP and WebDAV: no passkey mechanism to implement. Use a passkey-protected
   web page to make per-client secrets or tokens (FAST-style for XMPP); add
   the login limit of issue 1119 first.
9. Watch, do not build: AAuth, SASL PASSKEY, agent drafts. Revisit when a WG
   adopts one.

## 8. Draft OKR for owner approval

Objective: a person approves narrow, revocable access for an agent with a
passkey, and the storage records each use.

- KR 1. Grant-use record. Baseline: 0 (no record names a grant;
  `grantAllows` returns `Bool`). Target: every request that a grant permits
  writes one record with the grant ID, and a theorem links the cited grant to
  the decision. Measure: `node tests/lws/grant-audit.mjs` (new) exits 0, and
  `lake build` with the theorem in a build root
  (`python3 tools/lean-unbuilt-modules.py --gate` exits 0).
- KR 2. WebAuthn verification in Lean. Baseline: 0 of 5 (no module).
  Target: 5 of 5 vector sets of WebAuthn Level 3 §16.2 to §16.6
  (ES256 with attestation "none": plain, cross-origin, top-origin, long
  credential ID; and §16.3 packed self-attestation) pass registration and assertion
  checks, and each vector with one changed byte fails. Measure:
  `lake exe l4webauthn-probe` (new), run with `formal/lean4/` as working
  directory.
- KR 3. Passkey-approved grant, end to end. Baseline: 0 of 1. Target: an
  e2e test with a virtual authenticator creates a grant with a passkey
  assertion over its digest; a grant POST without a valid assertion gets
  403; a changed grant document after approval gets 403; revocation stops
  the agent's next request. Measure: `node tests/authz/passkey-grant.mjs`
  (new); Touchstone stays at 215 passed, 0 failed
  (`bash tools/lws-touchstone.sh --config auth --authz factoidal`).
- KR 4. Feature-combination invariants for delegation. Baseline: 0 of 5
  entries in https://github.com/danbri/factoidal/issues/1120 for invariants
  1-4 and 6. Target: 5 of 5, each with a Lean theorem or a failing-when-broken
  test plus an issue for the theorem. Measure: the checklist in issue 1120
  and the named tests.

## 9. What I could not find or verify

- No standard SASL mechanism for passkeys; only an expired individual draft.
- No WebDAV passkey mechanism (none expected).
- No public way for a third party to receive Google Takeout exports.
- No public document on how the consumer Gemini app connects to third-party
  storage.
- Apple and Android native passkey documentation: not read for this record.
- CTAP 2.3 changes: from a search summary only.
- OpenID Foundation whitepaper: abstract and summaries only.
- The last 17,695 characters of the LWS 1.0 core WD and parts of WebAuthn L3
  were not read by the fetch tool; the WebAuthn defaults and test vector list
  were read from the HTML source.
- The IETF individual agent drafts listed in Section 3.1: names and dates
  only.
