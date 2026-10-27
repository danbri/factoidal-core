---
title: Servers
description: The HTTP and XMPP servers of Factoidal — SPARQL Protocol and Graph Store with Fuseki paths, read-only Jena TDB2, Linked Web Storage, WebDAV, Solid and XMPP — with the exact commands and output recorded from real runs.
layout: hub.njk
tests: tests/hub/hub_servers_test.mjs
---

# Servers

[Hub](../) · SPARQL Protocol, Graph Store, Fuseki paths, TDB2, LWS, WebDAV, Solid, XMPP

A server cannot run in a browser page, so this page has no live cells.
Each section gives the command, what the server does and does not do, and
the output of a run made on 2026-10-20 with `@factoidal/core` 0.10.0 (the
LWS and WebDAV runs: 2026-10-27 with 0.18.0) from
this repository (`node npm/factoidal/bin/factoidal.mjs`, shown below as
`factoidal`) and the Lean native build. In each server, the protocol
decisions (routing, status codes, content negotiation, evaluation) are
made by Lean code; the Node host only moves bytes.

ActivityStreams: the tree has no ActivityStreams or ActivityPub server.

## SPARQL 1.1 Protocol and Graph Store, Fuseki paths

```
factoidal serve --file DATA /DATASET [--port N]      # like fuseki-server --file DATA /DATASET
factoidal serve STORE [--port N]                      # an activated Shardborough store
```

What it does: packs `DATA` into a temporary Shardborough collection and
serves `/DATASET/sparql` (also `/query` and `/update`) and the Graph Store
at `/DATASET/data` (read-write) and `/DATASET/get` (read only), the paths
Apache Jena Fuseki uses. A `GET` of the query endpoint with no query
answers the SPARQL 1.1 Service Description. An update is appended to the
store's delta log before the response. The read-only Fuseki
administration paths `/$/ping`, `/$/server`, `/$/datasets` and
`/$/stats` answer.

What it does not do: with `--file`, updates are lost when the process
exits. One dataset per process, and no Fuseki configuration file, text
index or inference configuration:
<https://github.com/danbri/factoidal/issues/832>. No administration
operation that changes the server:
<https://github.com/danbri/factoidal/issues/831>. A Graph Store `GET` in
JSON-LD answers 406: <https://github.com/danbri/factoidal/issues/830>.

```
$ factoidal serve --file data.ttl /ds --port 3031
packed 374 bytes of turtle into /tmp/factoidal-serve-7zuTTB/gen-1
20 artifacts, 4294 bytes, layout ibk5
5 rows
activated gen-1: 19 artifacts verified, 2424 bytes
http://127.0.0.1:3031

$ curl -s http://127.0.0.1:3031/ds/sparql -H "Accept: text/csv" \
    --data-urlencode "query=SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name"
name
Alice
Bob

$ curl -s -X POST http://127.0.0.1:3031/ds/update -w "%{http_code}\n" \
    --data-urlencode 'update=INSERT DATA { <http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" }'
204

$ curl -s "http://127.0.0.1:3031/ds/data?default" -H "Accept: application/n-triples"
<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .
<http://example.org/bob> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .
<http://example.org/bob> <http://xmlns.com/foaf/0.1/name> "Bob" .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> <http://example.org/bob> .
<http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" .

$ curl -s -X PUT "http://127.0.0.1:3031/ds/get?default" -H "Content-Type: text/turtle" \
    --data "<http://e/x> <http://e/p> 1 ." -w "%{http_code}\n"
/ds/get is read-only; write through /ds/data
405

$ curl -s http://127.0.0.1:3031/ds/sparql -H "Accept: text/turtle"
...
ns2:sparql a ns1:Service ;
    ns1:defaultDataset <http://127.0.0.1:3031/ds/sparql#dataset> ;
    ns1:endpoint ns2:sparql ;
    ns1:feature ns1:BasicFederatedQuery ;
    ns1:supportedLanguage ns1:SPARQL10Query , ns1:SPARQL11Query , ns1:SPARQL11Update .

$ curl -s 'http://127.0.0.1:3033/$/ping'
2026-10-20T22:17:37.139Z
$ curl -s -X POST 'http://127.0.0.1:3033/$/datasets?dbName=other' -w ' [%{http_code}]\n'
/$/datasets is read-only in this server [405]
```

`data.ttl` is four Turtle lines: Alice and Bob, typed `foaf:Person`, with
names, and Alice `foaf:knows` Bob.

## Jena TDB2, read only

```
factoidal serve --tdb2 DIR /DATASET [--port N]       # like fuseki-server --loc DIR /DATASET
```

What it does: reads an Apache Jena TDB2 database directory in place with
a Lean decoder of the TDB2 indexes and node table, and answers SPARQL
queries and Graph Store reads.

What it does not do: no writes (update and Graph Store writes answer
501); every quad is held in memory while the server runs; queries are not
answered from the on-disk indexes; triple terms are not decoded:
<https://github.com/danbri/factoidal/issues/834>.

```
$ tdb2.tdbloader --loc tdb2db data.ttl        # Apache Jena 6.2.0
$ factoidal serve --tdb2 tdb2db /ds --port 3032
http://127.0.0.1:3032
serve: listening on http://127.0.0.1:3032 for tdb2db (layout tdb2, 5 rows, delta batches replayed: 0, write scope read-only)

$ curl -s http://127.0.0.1:3032/ds/sparql -H "Accept: text/csv" \
    --data-urlencode "query=SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name"
name
Alice
Bob

$ curl -s -X POST http://127.0.0.1:3032/ds/update -w "%{http_code}\n" \
    --data-urlencode "update=INSERT DATA { <http://e/x> <http://e/p> 1 }"
this dataset is a read-only Jena TDB2 database read in place: it accepts queries and Graph Store reads,
and no update or Graph Store write. Load the data into a Shardborough collection (factoidal pack,
then factoidal serve STORE) to write.
501
```

## Linked Web Storage 1.0

```
factoidal lws-serve DIR (--authz DIR | --issuer IRI | --auth-config FILE | --insecure-no-auth) [--port N] [--base IRI]
```

What it does: answers every request through the engine's `lwsStep`
operation, from the
[LWS 1.0 core editor's draft](https://w3c.github.io/lws-protocol/lws10-core/):
containers, create, read, update and delete, `Last-Modified`, auxiliary
resource links, N3 Patch. The storage is written to `DIR` after every
change. One of the four authorization options is required. Since this page
was first written, storage authorization
(<https://github.com/danbri/factoidal/issues/886>), container pagination
(<https://github.com/danbri/factoidal/issues/887>), client-managed metadata
(<https://github.com/danbri/factoidal/issues/888>), binary bodies
(<https://github.com/danbri/factoidal/issues/889>) and notifications
(<https://github.com/danbri/factoidal/issues/890>) are closed;
`factoidal lws-serve --help` lists their options. Touchstone result: the
[package README](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/README.md#test-results).

Since 0.17.0, `--authz DIR` also serves an authorization server on the same
port. Its issuer is the storage root without the trailing slash; the token
endpoint and the JWK Set are under the storage root's `.well-known/`; the
engine decides which requests are the authorization server's (op
`authzOwns`). Both forms of each well-known path are read, so a reverse
proxy can serve the storage at a path prefix
(https://github.com/danbri/factoidal-core/releases/tag/v0.17.0). Run on
2026-10-27 with `@factoidal/core` 0.18.0:

```
$ factoidal lws-serve ./lws-store --authz ./lws-authz --port 3040
lws-serve: listening on http://127.0.0.1:3040 for ./lws-store
lws-serve: authorization server http://127.0.0.1:3040 (keys in ./lws-authz)
http://127.0.0.1:3040

$ curl -si http://127.0.0.1:3040/notes/a.ttl
HTTP/1.1 401 Unauthorized
content-type: application/problem+json
www-authenticate: Bearer resource_metadata="http://127.0.0.1:3040/.well-known/oauth-protected-resource/notes/a.ttl"
link: <http://127.0.0.1:3040/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"

{"type":"about:blank","title":"Unauthorized","status":401,"detail":"an access token is required","instance":"/notes/a.ttl"}

$ curl -s http://127.0.0.1:3040/.well-known/lws-configuration
{"issuer":"http://127.0.0.1:3040","token_endpoint":"http://127.0.0.1:3040/.well-known/lws-token",
 "jwks_uri":"http://127.0.0.1:3040/.well-known/lws-jwks",
 "grant_types_supported":["urn:ietf:params:oauth:grant-type:token-exchange"], ...}
```

Line breaks were added to the JSON for this page.

The LWS client (`factoidal lws-client`)
gained range and conditional reads, trusted storages for notifications,
one-page search, linksets, Ed25519 session keys and bearer tokens in
0.18.0 (https://github.com/danbri/factoidal/issues/1065).

## WebDAV for file browsers

```
factoidal webdav-serve CONFIGDIR [--port N] [--host ADDRESS]
```

What it does (since 0.18.0, https://github.com/danbri/factoidal/issues/1066):
serves LWS storages to file browsers over WebDAV, RFC 4918 classes 1 and
2. The root collection holds one folder per mount. A mount is one Markdown
file `CONFIGDIR/NAME.md`: `- kind: local` with `- path:` an `lws-serve`
storage directory, or `- kind: lws` with `- url:` a remote storage, reached
through the LWS client. Every method, status, property and lock is decided
in `L4Factoidal/WebDAV/`. litmus 0.13: 208 pass, 0 fail (out of 208, on a
local and a remote mount).

What it does not do: dead properties and locks are lost when the server
restarts: <https://github.com/danbri/factoidal/issues/1078>. It is not yet
checked with the real file browsers:
<https://github.com/danbri/factoidal/issues/1079>.

Run on 2026-10-27 with `@factoidal/core` 0.18.0. `alice-storage` is an
`lws-serve` storage that holds `/notes/a.ttl`:

```
$ cat dav/alice.md
# Alice
- kind: local
- path: ../alice-storage

$ factoidal webdav-serve ./dav --port 8090
webdav-serve: listening on http://127.0.0.1:8090 for ./dav
webdav-serve: http://127.0.0.1:8090/alice/ - Alice (local)
http://127.0.0.1:8090

$ curl -si -X OPTIONS http://127.0.0.1:8090/
HTTP/1.1 200 OK
dav: 1, 2
allow: OPTIONS, GET, HEAD, PUT, DELETE, MKCOL, COPY, MOVE, PROPFIND, PROPPATCH, LOCK, UNLOCK

$ curl -s -X PROPFIND -H 'Depth: 1' http://127.0.0.1:8090/alice/notes/
<?xml version="1.0" encoding="utf-8"?>
<D:multistatus xmlns:D="DAV:">
<D:response><D:href>/alice/notes/</D:href><D:propstat><D:prop><D:resourcetype><D:collection/></D:resourcetype>
  <D:displayname>notes</D:displayname> ...
<D:response><D:href>/alice/notes/a.ttl</D:href><D:propstat><D:prop><D:resourcetype/><D:displayname>a.ttl</D:displayname>
  <D:getcontenttype>text/turtle</D:getcontenttype><D:getcontentlength>44</D:getcontentlength> ...
</D:multistatus>

$ curl -s -o /dev/null -w '%{http_code}\n' -X PUT --data 'hello' http://127.0.0.1:8090/alice/notes/hello.txt
201
```

## Solid Protocol, server and client

```
factoidal solid-serve DIR [--port N] [--base IRI] [--owner WEBID]
factoidal solid-client <get|put|post|delete|discover|patch> URL [--body TEXT] [--content-type TYPE]
```

What it does: the server answers through `solidStep`: storage discovery,
containment triples, the `Allow` and `Accept-*` headers, the PUT, POST,
PATCH and DELETE rules, N3 Patch, Web Access Control, CORS and the LDN
inbox ([Solid Protocol 0.11](https://solidproject.org/TR/protocol)). The
client builds each request with `solidClientRequest` and reads each
response with `solidClientResponse`, and prints both as JSON.

What it does not do: the resource tree is held in memory (as for LWS).
Solid-OIDC authentication is decided by the engine from the request, but
the server does not run an identity provider; this run writes without
credentials to a test storage. The conformance ledger lists the open
rows: [docs/lws-solid-conformance.md](https://github.com/danbri/factoidal-core/blob/main/docs/lws-solid-conformance.md),
tracking <https://github.com/danbri/factoidal/issues/659>.

```
$ factoidal solid-serve ./solid-store --port 3041 --owner http://127.0.0.1:3041/profile/card#me
http://127.0.0.1:3041

$ factoidal solid-client put http://127.0.0.1:3041/docs/hello.ttl --content-type text/turtle --body "<#x> <http://e/p> 1 ."
{ "kind": "replace",
  "request": { "method": "PUT", "target": "http://127.0.0.1:3041/docs/hello.ttl", ... },
  "response": { "status": 201, ... ["location", "/docs/hello.ttl"] ... }, "steps": 1 }

$ curl -si -X PATCH http://127.0.0.1:3041/docs/hello.ttl -H "Content-Type: text/n3" --data-binary @patch.n3
HTTP/1.1 204 No Content

$ curl -s http://127.0.0.1:3041/docs/hello.ttl
@prefix ns1: <http://127.0.0.1:3041/docs/hello.ttl#> .
@prefix ns2: <http://e/> .

ns1:x ns2:p 1 ;
    ns2:q 2 .
```

`patch.n3` is a `solid:InsertDeletePatch` with
`solid:inserts { <#x> <http://e/q> 2 . }`.

## XMPP

```
l4xmpp-serve --domain DOMAIN --state DIR [--accounts FILE] [--plaintext]
```

What it does: one XMPP client connection on standard input and output
(RFC 6120, RFC 6121). A carrier process listens on the socket, terminates
TLS and starts one `l4xmpp-serve` per connection. Stream negotiation,
SASL PLAIN, resource binding and stanza routing between sessions (through
a spool directory) are decided in `L4Factoidal/XMPP/`. `l4xmpp-serve` is
a native Lean executable (`lake build l4xmpp-serve` in `formal/lean4`);
it is not in the npm package.

What it does not do: no PRECIS enforcement for JIDs:
<https://github.com/danbri/factoidal/issues/676>.

```
$ printf '%s' "$CLIENT_BYTES" | l4xmpp-serve --domain example.com --state ./xmpp-state --plaintext --stream-id s1 --nonce 1
--- client sends:
<?xml version='1.0'?><stream:stream to='example.com' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>
<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>AHJvbWVvAHNlY3JldA==</auth>
<stream:stream to='example.com' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>
<iq type='set' id='b1'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'><resource>orchard</resource></bind></iq>
</stream:stream>
--- server writes:
<?xml version='1.0'?><stream:stream xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams'
  from='example.com' id='s1' version='1.0' xml:lang='en'><stream:features><mechanisms
  xmlns="urn:ietf:params:xml:ns:xmpp-sasl"><mechanism>SCRAM-SHA-256</mechanism><mechanism>PLAIN</mechanism>
  </mechanisms></stream:features>
<success xmlns='urn:ietf:params:xml:ns:xmpp-sasl'/>
<?xml version='1.0'?><stream:stream ... id='s1' version='1.0' xml:lang='en'><stream:features><bind
  xmlns="urn:ietf:params:xml:ns:xmpp-bind"/><session xmlns="urn:ietf:params:xml:ns:xmpp-session"/></stream:features>
<iq type="result" id="b1"><bind xmlns="urn:ietf:params:xml:ns:xmpp-bind"><jid>romeo@example.com/orchard</jid></bind></iq>
</stream:stream>
```

The accounts file held `romeo:secret`; the `auth` element carries
`\0romeo\0secret` in base64. Line breaks were added to the server output
for this page.

## Shardborough store commands

`factoidal pack`, `activate`, `query`, `update` and `compact` operate on a
persisted store. See [Shardborough](../shardborough/).
