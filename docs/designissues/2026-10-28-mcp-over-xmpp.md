# MCP over XMPP: literature review and transport options

Date: 2026-10-28. Issue: https://github.com/danbri/factoidal/issues/1121.
Status: review and proposal. No code. Related: HTTP over XMPP
(https://github.com/danbri/factoidal/issues/1107,
`docs/designissues/2026-10-28-http-over-xmpp.md`), feature-combination safety
(https://github.com/danbri/factoidal/issues/1120), capability-aware planner
(https://github.com/danbri/factoidal/issues/800).

Owner, 2026-10-28, verbatim: "there is value in implementing both sides of
mcp-over-xmpp (“xmpcp”?), please progress that - issues, subagent, lit
review." The name "xmpcp" is the owner's suggestion, with a question mark. This
record does not use it as a term.

All web sources were read on 2026-10-28. The source list is at the end.

## 1. Summary

1. The current MCP revision is **2026-07-28**. It is stateless. It removes the
   `initialize` handshake, protocol sessions and server-initiated JSON-RPC
   requests. Sampling, elicitation and roots now come back inside a result
   (`resultType: "input_required"`), and the client retries the request. Every
   exchange is a client request followed by server notifications and one
   response. This change makes an XMPP binding much simpler than it was under
   2025-11-25.
2. The specification permits custom transports. A custom transport MUST keep
   the JSON-RPC message format, the message patterns and the per-request
   metadata, and SHOULD document connection establishment, framing and
   cancellation.
3. I found no MCP-over-XMPP specification, ProtoXEP, XEP, mailing-list thread
   or implementation. The XMPP projects that I found are MCP servers that give
   an LLM XMPP tools (stdio transport), not MCP carried over XMPP. The only
   published MCP binding to a messaging system that I found is EMQX "MCP over
   MQTT". The MCP WebSocket proposal (SEP-1288) was closed as dormant on
   2026-06-26.
4. The XMPP building blocks that fit (XEP-0335 JSON Containers, XEP-0332 HTTP
   over XMPP, XEP-0432 Simple JSON Messaging) are all **Deferred**. XEP-0050
   Ad-Hoc Commands and XEP-0004 Data Forms are stable, but a data form cannot
   express a general JSON Schema 2020-12 `inputSchema`.
5. MCP authorization (OAuth 2.1, RFC 9728, RFC 8707) is defined for HTTP
   transports only. For "alternative transports" the specification says they
   "MUST follow established security best practices for their protocol". For
   XMPP that is the server-stamped `from` JID (RFC 6120 §8.1.2.1).

Recommendation: option (b), JSON-RPC in `<iq>` stanzas with an XEP-0335
payload, in a namespace of our own. Build it after a Lean MCP core that is
tested over stdio and Streamable HTTP with the official conformance tool. Option
(a) comes free when the XEP-0332 proxy of issue 1107 exists, and is useful as a
differential test, not as the main path. Option (c) is deferred. Section 6
gives the order.

## 2. MCP, revision 2026-07-28

Source: https://modelcontextprotocol.io/specification/latest resolves to
revision 2026-07-28; the schema is
https://github.com/modelcontextprotocol/specification/blob/main/schema/2026-07-28/schema.ts.
The previous revision is 2025-11-25 (changelog).

Note: the README of the official conformance tool
(`@modelcontextprotocol/conformance@0.2.0-alpha.12`) calls 2026-07-28 a
"draft", and its stable release 0.1.16 targets 2025-11-25. The specification
site lists 2026-07-28 as the current revision. Check this before a gate pins a
version.

### 2.1 Base protocol

- JSON-RPC 2.0, UTF-8. A request `id` is a string or integer, never `null`,
  and is unique among the sender's open requests. Every result has
  `resultType` (`"complete"` or `"input_required"`).
- Statelessness: "all the information needed to process a request is contained
  in the request itself." Each request carries `_meta`
  `io.modelcontextprotocol/protocolVersion` and
  `io.modelcontextprotocol/clientCapabilities` (required), and
  `io.modelcontextprotocol/clientInfo` (should). A missing required field gives
  `-32602`. `server/discover` (servers MUST implement it) returns the versions,
  capabilities and identity.
- `clientInfo` and `serverInfo` are self-reported and "SHOULD NOT" be used for
  security decisions.
- Error codes `-32020` to `-32099` are reserved for MCP: `-32020`
  HeaderMismatch, `-32021` MissingRequiredClientCapability, `-32022`
  UnsupportedProtocolVersion.
- Message size: the base protocol, stdio and Streamable HTTP pages state no
  maximum message size. I found none.

### 2.2 Message patterns

- Request and response; Multi Round-Trip Requests (MRTR); subscribe and
  notify.
- MRTR: a server that needs input returns `InputRequiredResult` with
  `inputRequests` (each an `elicitation/create`, `sampling/createMessage` or
  `roots/list` request) and an opaque `requestState`. The client retries with
  a new `id`, `inputResponses` and the same `requestState`. Only
  `tools/call`, `resources/read` and `prompts/get` may return it. The server
  MUST treat `requestState` as attacker-controlled and protect its integrity
  (HMAC or AEAD) when it affects authorization, and SHOULD bind it to the
  authenticated principal, an expiry and the originating request.
- `subscriptions/listen` is one long-lived request whose response stream
  carries list-changed and resource-updated notifications, tagged with
  `io.modelcontextprotocol/subscriptionId`. Progress and log notifications go
  only on the stream of the request they relate to.
- Cancellation: on stdio the client MUST send `notifications/cancelled` with
  the request id; on Streamable HTTP closing the response stream is the
  cancellation. A server sends `notifications/cancelled` only to end a
  `subscriptions/listen`. Both sides MUST tolerate the race where the result
  is already sent. Requests SHOULD have timeouts.

### 2.3 Features

- Server: tools, resources, prompts. A tool has `name`, `description`,
  `inputSchema` (JSON Schema, default dialect 2020-12), optional
  `outputSchema` and `annotations`. Clients MUST treat annotations as
  untrusted unless the server is trusted. `tools/list` MUST NOT vary per
  connection, but MAY vary with the authorization on the request.
  `tools/list` results carry `ttlMs` and `cacheScope`.
- Tool security (tools page): servers MUST validate inputs, implement access
  controls, rate limit invocations and sanitize outputs.
- Client: elicitation (form and URL mode). Form mode is limited to "flat
  objects with primitive properties" and MUST NOT ask for passwords, keys or
  tokens. Sampling, roots and logging are **Deprecated** in 2026-07-28
  (SEP-2577); new implementations should not add them.
- Tasks moved to an extension (`io.modelcontextprotocol/tasks`).
- `$ref` to a network URI MUST NOT be dereferenced by default.

### 2.4 Transports

- stdio: one JSON-RPC message per line, no embedded newlines. The page says
  the framing "works unchanged over Unix domain sockets, TCP connections, or
  any similar channel".
- Streamable HTTP: one endpoint, every message is a POST. A request gets
  `application/json` or a request-scoped `text/event-stream`. Required
  headers: `MCP-Protocol-Version`, `Mcp-Method`, and `Mcp-Name` for
  `tools/call`, `resources/read` and `prompts/get`; they MUST match the body
  (`-32020` otherwise). The server MUST validate `Origin` and SHOULD bind to
  127.0.0.1 when local. No `Mcp-Session-Id`, no GET stream, no
  `Last-Event-ID` resumption.
- HTTP+SSE (2024-11-05) was replaced by Streamable HTTP in 2025-03-26 and is
  now Deprecated (SEP-2596).
- Custom transports: "Implementers who choose to support custom transports
  MUST preserve the JSON-RPC message format, the message patterns, and the
  per-request metadata model. Custom transports SHOULD document their
  connection establishment, message framing, and cancellation patterns".
  Over a reliable byte stream they SHOULD reuse stdio framing.

### 2.5 Authorization

- Defined "for HTTP-based transports". stdio "SHOULD NOT" follow it.
  "Implementations using alternative transports MUST follow established
  security best practices for their protocol."
- The MCP server is an OAuth 2.1 resource server. It MUST publish RFC 9728
  Protected Resource Metadata; clients MUST send RFC 8707 `resource`; servers
  MUST check the token audience and MUST NOT pass the client's token to
  upstream APIs ("token passthrough"). Client ID Metadata Documents are
  preferred; RFC 7591 dynamic registration is Deprecated. RFC 9207 `iss`
  validation is required of clients.
- Overlap with LWS: Factoidal's LWS server and authorization server already
  use RFC 9728 metadata and RFC 8693 token exchange
  (`formal/lean4/L4Factoidal/LWS/Authorization.lean`,
  `L4Factoidal/Authz/Server.lean`, issue 916). MCP's authorization page does
  not name RFC 8693. The same authorization server could issue MCP tokens if
  it supports the `resource` parameter and audience per resource. An MCP
  server that calls LWS on a user's behalf needs a separate LWS token (no
  passthrough); RFC 8693 is a candidate way to get it, which is our choice,
  not MCP's.

## 3. Existing work

### 3.1 MCP over XMPP

Searches on 2026-10-28 (web search for "Model Context Protocol" with XMPP,
standards@xmpp.org, ejabberd, Prosody, Openfire; the XSF XEP list
https://xmpp.org/extensions/xeplist.xml; the ProtoXEP inbox
https://xmpp.org/extensions/inbox/) found no MCP transport over XMPP. The
method cannot see private work, unindexed list mail, or XSF summit notes; I did
not read the standards@xmpp.org archive directly.

Found, and not a transport:

- https://github.com/abligh/xmpp-mcp (MIT, Python): an MCP server that gives
  an LLM XMPP tools (chat, roster, disco, pubsub with data forms). "The server
  speaks the MCP stdio transport."
- https://github.com/cronus42/jabber-mcp: an MCP stdio server that sends
  messages over XMPP.
- https://lab.tagroot.io/MCP/XMPP: an MCP server resource for XMPP network
  access (search result only; not opened).
- ProtoXEP "Communicate & Ask to AI" (https://xmpp.org/extensions/inbox/xep-ai.html),
  version 0.0.1, 2023-03-13, namespace `urn:xmpp:ai:0`, not accepted. It asks
  a model a question in a `<message>`; it has no tools and does not mention MCP.

### 3.2 MCP over other messaging systems

- MQTT: EMQX "MCP over MQTT"
  (https://docs.emqx.com/en/emqx/latest/emqx-ai/mcp-over-mqtt/specification.html).
  It is built on the session model (`initialize` example with
  `protocolVersion` 2024-11-05; it cites the 2025-06-18 specification).
  Topics: `$mcp-server/{server-id}/{server-name}` for control,
  `$mcp-server/presence/...` with retained messages for discovery,
  `$mcp-rpc/{client-id}/{server-id}/{server-name}` per client and server
  pair. Authorization is broker ACLs plus roles. No size limit; it asks for a
  short presence message. Will messages mark disconnects. This is the closest
  analogue: presence-based discovery and a per-pair channel map to XMPP disco
  and full JIDs.
- WebSocket: SEP-1288
  (https://github.com/modelcontextprotocol/modelcontextprotocol/issues/1288),
  opened 2025-08-02, closed 2026-06-26 as dormant with no core-maintainer
  sponsor. The open question was authentication: browsers cannot set headers
  on a WebSocket.
- NATS and Matrix: I found no MCP binding. The NATS results are MCP servers
  that give NATS tools.

## 4. XMPP building blocks

Status and version from https://xmpp.org/extensions/xeplist.xml, read
2026-10-28.

| Spec | Status, version, date | Fit for MCP |
|---|---|---|
| RFC 6120 XMPP Core | RFC, 2011 | `<iq>` is request-response; the server stamps `from` (§8.1.2.1); in-order delivery per sender and recipient over a stream (§10.1); maximum stanza size not less than 10,000 bytes, set by the administrator, over-limit gives `policy-violation` (§13.12). |
| RFC 6121 IM | RFC, 2011 | An `<iq>` to a full JID with no such resource gets `service-unavailable` (§8.5.3.2.3); a `<message>` may go to offline storage. |
| XEP-0009 Jabber-RPC | Final, 2.2.1, 2021-03-04 | XML-RPC in `<query xmlns='jabber:iq:rpc'>`. XML-RPC has no null and its schema limits strings to printable ASCII. JSON-RPC does not map without loss. Discovery identity `automation/rpc`. |
| XEP-0050 Ad-Hoc Commands | Draft, 1.3.0, 2020-06-09 | Commands as disco nodes, `sessionid`, actions `execute/next/prev/complete/cancel`, status `executing/completed/canceled`. Any namespaced payload is allowed. "Deciding who may execute a command is out of scope." |
| XEP-0004 Data Forms | Final, 2.13.2, 2024-08-30 | Flat field list. Fits MCP form-mode elicitation; does not fit a general `inputSchema`. |
| XEP-0122 Data Forms Validation | Draft, 1.0.2, 2018-03-21 | Datatypes and ranges for form fields. |
| XEP-0332 HTTP over XMPP | Deferred, 0.5.1, 2020-03-31 | Carries Streamable HTTP POSTs; `chunkedBase64` can carry an SSE body. Section 5 (a). |
| XEP-0335 JSON Containers | Deferred, 0.1.1, 2018-09-26 | `<json xmlns='urn:xmpp:json:0'>`, character data only, UTF-8, not empty; SHOULD be wrapped in a context element, not a direct child of a stanza; recipients SHOULD validate. |
| XEP-0432 Simple JSON Messaging | Deferred, 0.1.1, 2022-04-12 | `<payload xmlns='urn:xmpp:json-msg:0' datatype='...'>` in a `<message>`; disco feature `urn:xmpp:json-msg:0#<datatype>`. The XEP says it should not be used as a base for other standards. |
| XEP-0030 Service Discovery | Final, 2.5.0, 2024-04-30 | Announce an MCP endpoint by a feature string. The disco category registry has `automation` (command-list, command-node, rpc, soap, translation) and `client/bot`; no AI or MCP type. |
| XEP-0115 Entity Capabilities | Draft, 1.6.0, 2022-03-08 | Caches the disco features in presence. XEP-0390 (Caps 2.0) is Deferred. |
| XEP-0198 Stream Management | Draft, 1.6.3, 2025-07-28 | Acks and resumption. Unacknowledged stanzas after a failed resumption are treated as sent to an unavailable resource; duplicates are possible. |
| XEP-0047 IBB | Final, 2.0.1, 2021-01-12 | Large bodies in base64 blocks. |
| XEP-0065 SOCKS5 Bytestreams | Draft, 1.8.2, 2021-03-04 | Large bodies out of band; needs a proxy or direct connection. |
| XEP-0234 Jingle File Transfer | Deferred, 0.19.1, 2019-06-19 | Large files. |
| XEP-0363 HTTP File Upload | Draft, 1.2.0, 2025-06-17 | Large results by URL (a `resource_link`). |
| XEP-0060 PubSub | Draft, 1.30.0, 2025-11-11 | Could carry list-changed notifications to many subscribers; not needed for one client. |
| XEP-0235 OAuth over XMPP | Deferred, 0.7, 2009-03-24 | Old; not a basis. |
| XEP-0493 OAuth Client Login | Experimental, 0.1.1, 2025-03-31 | Grants a third party access to an XMPP account. Not MCP authorization. |

Factoidal's XMPP server today handles `jabber:iq:roster` and
`http://jabber.org/protocol/disco#info` (grep of `L4Factoidal/XMPP/*.lean`,
2026-10-28). I found no XEP-0198, XEP-0050 or XEP-0335 code.

## 5. Options for Factoidal

Common facts for all three:

- A JID is an authenticated identity: the sender's server stamps `from` with
  the full JID after SASL (RFC 6120 §8.1.2.1). Across domains the receiving
  server trusts the sending domain's server. So "authorization by JID" means
  "trust the account's server and its SASL".
- The 10,000-byte floor is the only size guarantee. A `tools/list` with
  schemas, or a SPARQL result, can exceed it.
- MCP 2026-07-28 has no server-initiated requests, so the server never needs
  to start an exchange towards the client JID, except notifications on an
  open `subscriptions/listen`.

### (a) Streamable HTTP over XEP-0332

Each MCP POST is a `<req method='POST' resource='/mcp'>` with the MCP headers
in the XEP-0131 shim and the JSON body as `text`. A JSON response is a `<resp>`;
an SSE response is a `chunkedBase64` stream of `chunk` messages.

- Initialization: none (stateless). `server/discover` is an ordinary POST.
- Server to client: MRTR results come in the response; listen notifications
  come as SSE chunks.
- Cancellation: XEP-0332 has a `close` message that stops a chunked stream
  (the stage 1 codec has `renderClose`). Mapping "close" to "cancel" is our
  rule; the XEP does not say it.
- Ordering: chunks are numbered (`nr`); responses to concurrent requests may
  arrive in any order.
- Size: XEP-0332 chunking (`maxChunkSize` 256 to 65,536).
- Discovery: XEP-0332 feature only; nothing says "this JID has MCP at /mcp".
- Authorization: MCP's OAuth profile applies as written (it is HTTP), with
  RFC 9728 metadata at a `/.well-known` path over `httpx`. The JID check of
  issue 1107 is a second layer. `Origin` has no meaning here.
- Pros: no new MCP binding; the official tools run unchanged through the
  local proxy of issue 1107 stage 2.
- Cons and risks: Deferred XEP with no other known implementation; three
  encodings (JSON in HTTP in XML, plus base64 for SSE); depends on the whole
  1107 stack (client stream and proxy); bearer tokens travel in stanzas
  through XMPP servers.

### (b) JSON-RPC in stanzas, our own namespace

Proposed shape (a sketch, not a decision). Request:

```xml
<iq type='set' id='x1' to='mcp@example.org/factoidal'>
  <rpc xmlns='urn:x-factoidal:mcp:0'>
    <json xmlns='urn:xmpp:json:0'>{"jsonrpc":"2.0","id":1,"method":"tools/call",...}</json>
  </rpc>
</iq>
```

The final JSON-RPC response is in the `<iq type='result'>`. Notifications for
that request (progress, log) are `<message>` stanzas with the same wrapper,
sent before the `iq` result. `notifications/cancelled` from the client is a
`<message>`, as on stdio. The namespace name is a placeholder; a ProtoXEP would
give an `urn:xmpp:` name.

- Initialization: none. `server/discover` is one `iq`. The stdio framing rule
  ("reuse stdio framing") is for byte streams; a stanza is already a frame.
- Server to client: MRTR in the `iq` result. A `subscriptions/listen` keeps
  its `iq` open until the subscription ends; notifications are messages to the
  requesting full JID. Risk: client libraries that time out an `iq`. Option:
  answer the listen `iq` with an acknowledgement and send notifications as
  messages until `notifications/cancelled`; that is a documented binding rule
  of ours.
- Cancellation: `notifications/cancelled` as on stdio. If the client's
  resource goes unavailable (presence), the server cancels its open requests;
  this follows the Streamable HTTP rule that a closed stream cancels.
- Ordering: RFC 6120 §10.1 gives in-order delivery between one sender and one
  recipient, so progress messages arrive before the `iq` result when both go
  over the same path. Requests may run concurrently; JSON-RPC `id` correlates.
- Size: answer over-limit results with a `resource_link` (XEP-0363 upload or
  an LWS resource) or with a JSON-RPC error that names the limit. No chunking
  in version 1.
- Discovery: disco#info feature `urn:x-factoidal:mcp:0`; XEP-0115 caps in
  presence. The tool list is fetched with `tools/list`, not put into disco.
- Authorization: requests only from JIDs on an allow list per tool class
  (read, write); the `from` JID is the principal for MRTR `requestState`
  binding, rate limits and audit. No OAuth inside stanzas in version 1. If an
  MCP tool calls LWS, the MCP server gets its own LWS token for that
  principal; it never forwards a token it received.
- Delivery: use `<iq>` for requests, so a request to an absent resource fails
  at once (`service-unavailable`) and never waits in offline storage to run
  later.
- Pros: one JSON encoding; each MCP message is one stanza; maps directly to
  the stateless 2026-07-28 model; the same Lean dispatcher serves stdio, HTTP
  and XMPP.
- Cons and risks: no standard; another XMPP implementation will not speak it
  unless we publish a ProtoXEP; XEP-0335 is Deferred (but trivial); the
  official MCP tools need a local bridge to reach it.

### (c) XEP-0050 Ad-Hoc Commands

Each tool is a command node; the `inputSchema` becomes a data form.

- Initialization: disco#items on `http://jabber.org/protocol/commands`.
- Server to client: MRTR form-mode elicitation maps well to a multi-stage
  command (both are flat forms). Sampling and roots do not map.
- Cancellation: `action='cancel'`, required by the XEP.
- Ordering and sessions: XEP-0050 keeps a `sessionid`; MCP 2026-07-28 has no
  sessions, so the server must still carry state in `requestState`-like data.
- Size: same stanza limits.
- Discovery: the best of the three for humans: general XMPP clients that
  implement XEP-0050 can list and run the commands.
- Authorization: by JID; the XEP leaves it to the server.
- Pros: stable XEPs; a human can run a tool from a chat client.
- Cons: not MCP; a JSON Schema 2020-12 `inputSchema` (nested objects, arrays
  of objects, `oneOf`, `$ref`) does not fit XEP-0004; results lose
  `structuredContent` unless we add a JSON payload, which turns it into (b)
  with a command wrapper.

## 6. Recommended order

Owner's rule for this work: fastest and safest first.

1. **Lean MCP core, read-only, stdio.** In Lean: JSON-RPC 2.0 codec (on
   `L4Factoidal/JSON`), the 2026-07-28 message types, a pure dispatcher
   `step : Request → List Message` for `server/discover`, `tools/list`,
   `tools/call`, `resources/list`, `resources/read`; input validation with
   `L4Factoidal/JSONSchema`; tool descriptions generated from the op table.
   Read-only tools only (parse, query, validate, closure on a given input).
   Host: read lines, call the wasm, write lines. stdio needs no network and,
   per the specification, takes credentials from the environment.
   Tests: `#guard`s; MCP Inspector (`@modelcontextprotocol/inspector`, 2.12.0
   on npm) in CLI mode over stdio.
2. **Streamable HTTP on 127.0.0.1.** In Lean: header-body checks (`-32020`),
   `Origin` check, 202 for notifications, version errors, backward-compatibility
   answers (405 for GET and DELETE). Host: the existing HTTP server. JSON
   responses first; SSE only for progress. Acceptance:
   `npx @modelcontextprotocol/conformance server --url http://127.0.0.1:PORT/mcp`
   with `--expected-failures` YAML, each entry with an open issue (the
   expected-failure rule of 2026-09-07). Pin the conformance version.
3. **Option (b) server, inside our own `xmpp-serve`.** The MCP endpoint is an
   address served by our XMPP server, so no outgoing client stream is needed
   yet. In Lean: the stanza codec (XEP-0335 wrapper), the JID allow list, the
   rate limit per bare JID, cancellation on unavailable presence, size refusal.
   Host: nothing new beyond the session feed.
4. **Client side and bridge.** In Lean: MCP client state machine (build
   requests with `_meta`, handle `input_required` and retry with a new id,
   parse results). Host: `factoidal mcp-xmpp-bridge` that listens on
   127.0.0.1 as Streamable HTTP or stdio and sends stanzas to a JID.
   Acceptance: the same conformance run as step 2, through the bridge to step 3,
   with the same expected-failures file. The two runs must agree; that is the
   differential test of the XMPP binding.
5. **Remote side.** The outgoing client stream of issue 1107 stage 2 lets a
   Factoidal behind NAT offer MCP through any XMPP server. Test against our
   server, then one other server (Prosody or ejabberd).
6. **Planner.** Issue 800 reads `tools/list` from any of the three transports;
   descriptions and annotations are untrusted input unless the server is on a
   trusted list.
7. **Write tools last**, after the invariants of issue 1120 for them exist.
8. Option (a): test it when the 1107 proxy exists, as a third path in the
   same conformance run. Option (c): deferred; reconsider for human use with
   flat-schema tools only.
9. A ProtoXEP for (b), if the binding is stable after step 5.

## 7. Safety notes for issue 1120

- **Write tools.** A tool that changes a store or an LWS storage is callable
  only by JIDs on a write allow list, separate from the read list. The list
  is per tool class, decided in Lean, and checked on every request
  (statelessness gives no earlier point to check). Default: empty. Tool
  annotations (`destructiveHint` and others) are not an access control.
- **Composition with `webdav-serve` and LWS.** An MCP tool that reads or writes
  a storage must not act as the storage owner (`insecureNoAuth`) because the
  caller is an allowed JID. Invariant: the storage sees the MCP caller's own
  authority, or a narrower one, never the server's.
- **Confused deputy and LWS tokens.** MCP forbids token passthrough. Invariant:
  a token that our MCP server holds for LWS is bound to one principal (the
  `from` JID or the OAuth `sub`) and one storage; it never appears in a tool
  result, a log notification or a `requestState`; it is never sent to another
  JID.
- **`requestState`.** AEAD or HMAC; bind to the bare JID, an expiry and a
  digest of the method and arguments. A state presented by another JID fails.
- **Prompt injection in tool results.** Tool results (SPARQL results, parsed
  documents, LWS content) carry third-party text into a model's context. The
  server cannot remove this risk. It can label content with its source
  (`annotations.audience`, a `resource_link` in place of inline text) and
  keep result size bounded. Our MCP client and the planner treat every tool
  result and tool description as data, never as instructions.
- **Rate limits.** Per bare JID (all resources of one account count
  together), and per remote domain for federated callers, because one domain
  can create many accounts. This answers the 1120 question about the login
  rate limit keyed by address: over XMPP the key is the JID.
- **Open proxy and SSRF.** A tool that fetches a URL, follows SERVICE, or
  resolves a `$ref` gives a remote JID a path into the local network. MCP
  already forbids network `$ref` by default. Same rule for tools: no private
  addresses unless an allow list names them.
- **Offline delivery.** Requests in `<iq>` only, so a stored message cannot
  run a tool hours later.
- **Review notice.** The new server and client surfaces carry the
  experimental-code notice of 2026-10-27.

## 7a. Scope added by the owner, 2026-10-28

Owner, verbatim: "maybe i meant xmpp+mcp as “xmcpp”; needs a bacronym" and
"Note also we will want mcp controls for factoidal CLIs too; or subsets. And
webmcp options for our browser-visible servers."

- **Name.** "XMCPP" is the owner's working name for MCP over XMPP. The owner
  chooses its expansion; one literal candidate is "XMPP Model Context Protocol
  Profile". This record keeps "MCP over XMPP" until the owner decides.
- **MCP for the `factoidal` CLI.** Step 1 above (the Lean MCP core over
  stdio) is where CLI commands become tools: every command, or a subset the
  operator selects. Each tool's `inputSchema` is generated from the command's
  options, and the decisions stay in Lean.
- **WebMCP for the servers that browsers can see.** `lws-serve`, `solid-serve`,
  `serve` and `webdav-serve` can serve a page that registers their operations
  as WebMCP tools in the browser, opt-in for each server. The same tool
  descriptions as the MCP core; the same safety rules as section 7 (write tools
  behind authorization; results are data, not instructions).

- **Stateless first, classic as a compatibility layer.** Owner, 2026-10-28,
  verbatim: "Stateless mcp is future of mcp afaik; can we align even if
  support classic for historical reasons and legacy deployments?" Decision
  (coordinator, to that question): the Lean MCP core implements only the
  2026-07-28 stateless model (per-request `_meta`, `server/discover`,
  `input_required` results). A separate compatibility layer accepts the
  2025-11-25 flow (`initialize`, `notifications/initialized`,
  `Mcp-Session-Id`) and maps it onto the core: it keeps the negotiated
  version and client capabilities per session and adds them to each request
  as `_meta`. Server-initiated requests (sampling, elicitation) are not sent
  on the classic path; the layer returns a JSON-RPC error that names
  https://github.com/danbri/factoidal/issues/1121. The XMPP binding (option
  b) is stateless only, because no XMPP client of the classic model exists.
  Reason: the stable official SDKs and the conformance tool 0.1.16 still
  target 2025-11-25 (section 2), so stdio and HTTP clients need the layer
  now. The layer has its own tests and is removable with no change to the
  core.

## 8. What I could not find

- Any MCP-over-XMPP specification, ProtoXEP or implementation, or any
  standards@xmpp.org thread or XSF summit note on MCP (method in section 3.1).
- Any NATS or Matrix MCP transport.
- A message size limit in the MCP specification.
- Any second implementation of XEP-0332 (also open in issue 1107).
- Whether the conformance tool's "draft" label for 2026-07-28 is stale.

## Sources (all read 2026-10-28)

MCP:
- https://modelcontextprotocol.io/specification/latest
- https://modelcontextprotocol.io/specification/2026-07-28/changelog
- https://modelcontextprotocol.io/specification/2026-07-28/basic
- https://modelcontextprotocol.io/specification/2026-07-28/basic/transports
- https://modelcontextprotocol.io/specification/2026-07-28/basic/transports/stdio
- https://modelcontextprotocol.io/specification/2026-07-28/basic/transports/streamable-http
- https://modelcontextprotocol.io/specification/2026-07-28/basic/patterns/mrtr
- https://modelcontextprotocol.io/specification/2026-07-28/basic/patterns/cancellation
- https://modelcontextprotocol.io/specification/2026-07-28/basic/authorization
- https://modelcontextprotocol.io/specification/2026-07-28/basic/authorization/security-considerations
- https://modelcontextprotocol.io/specification/2026-07-28/server/tools
- https://modelcontextprotocol.io/specification/2026-07-28/client/elicitation
- https://cdn.jsdelivr.net/npm/@modelcontextprotocol/conformance@0.2.0-alpha.12/README.md
- npm registry: `@modelcontextprotocol/conformance` (latest 0.1.16, alpha
  0.2.0-alpha.12), `@modelcontextprotocol/inspector` (2.12.0)
- https://github.com/modelcontextprotocol/modelcontextprotocol/issues/1288

XMPP:
- https://xmpp.org/extensions/xeplist.xml
- https://xmpp.org/extensions/inbox/
- https://xmpp.org/extensions/inbox/xep-ai.html
- https://xmpp.org/registrar/disco-categories.xml
- https://xmpp.org/extensions/xep-0009.html
- https://xmpp.org/extensions/xep-0050.html
- https://xmpp.org/extensions/xep-0198.html
- https://xmpp.org/extensions/xep-0332.html (via the 1107 design record)
- https://xmpp.org/extensions/xep-0335.html
- https://xmpp.org/extensions/xep-0432.html
- https://www.rfc-editor.org/rfc/rfc6120.txt
- https://www.rfc-editor.org/rfc/rfc6121.txt

Other:
- https://docs.emqx.com/en/emqx/latest/emqx-ai/mcp-over-mqtt/specification.html
- https://github.com/abligh/xmpp-mcp
- https://github.com/cronus42/jabber-mcp (search result only)
- https://lab.tagroot.io/MCP/XMPP (search result only)
