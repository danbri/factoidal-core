---
title: Servers
description: The HTTP and XMPP servers of Factoidal — SPARQL Protocol and Graph Store with Fuseki paths, read-only Jena TDB2, Linked Web Storage, Solid and XMPP — with the exact commands and output recorded from real runs.
layout: hub.njk
tests: tests/hub/hub_servers_test.mjs
---

# Servers

<p class="warning"><strong>⚠️ EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the whole core
library and every command line tool, and in particular all protocol,
authentication and security code.</p>

[Hub](../) · SPARQL Protocol, Graph Store, Fuseki paths, TDB2, LWS, authorization server (OIDC, CID, SAML), Solid, XMPP

A server cannot run in a browser page, so this page has no live cells.
Each section gives the command, what the server does and does not do, and
the output of a run made on 2026-10-20 with `@factoidal/core` 0.10.0 from
this repository (`node npm/factoidal/bin/factoidal.mjs`, shown below as
`factoidal`) and the Lean native build. In each server, the protocol
decisions (routing, status codes, content negotiation, evaluation) are
made by Lean code; the Node host only moves bytes.

ActivityStreams: the tree has no ActivityStreams or ActivityPub server.

## Requests from web pages

`factoidal serve`, `webdav-serve`, and `lws-serve` and `solid-serve` with
`--insecure-no-auth` answer only their own host names: `localhost`,
`127.0.0.1`, `[::1]`, the `--host` address and the addresses of the
machine. Another `Host` gets 421 Misdirected Request, so a web page cannot
reach them through DNS rebinding. A request with a method other than GET,
HEAD and OPTIONS whose `Origin` is another origin gets 403, so a form on
another site cannot POST `update=DROP ALL`. `lws-serve --insecure-no-auth`
sends no CORS fields unless `--cors-origin ORIGIN` names a page. Add a name
with `--allow-host NAME` (a reverse proxy, Tailscale) and an origin with
`--allow-origin ORIGIN`. curl and other clients that send no `Origin` work as
before. Record: https://github.com/danbri/factoidal/issues/1124. Open:
`solid-serve --insecure-no-auth` still echoes any `Origin` (Solid Protocol
§8.1), so a page on another origin can read it.

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
factoidal lws-serve DIR [--port N] [--base IRI]
```

What it does: answers every request through the engine's `lwsStep`
operation, from the
[LWS 1.0 core editor's draft](https://w3c.github.io/lws-protocol/lws10-core/):
containers, create, read, update and delete, `Last-Modified`, auxiliary
resource links, N3 Patch without blank nodes in insertions.

`DIR` keeps the storage: one snapshot file `DIR/lws-state.json` (the
default), or with `--storage files` one file per body, a journal and a
metadata file. Design record:
[2026-10-22-lws-storage-on-disk.md](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-10-22-lws-storage-on-disk.md).

What it does not do (this list is from 2026-10-20 and some of its issues are
closed; see each issue): no storage-server authorization (401 challenge,
token validation): <https://github.com/danbri/factoidal/issues/886>. No
container pagination: <https://github.com/danbri/factoidal/issues/887>.
No client-managed metadata:
<https://github.com/danbri/factoidal/issues/888>. Resource bodies are
UTF-8 strings, so binary content is not stored faithfully:
<https://github.com/danbri/factoidal/issues/889>. No notifications or
access grants: <https://github.com/danbri/factoidal/issues/890>.

```
$ factoidal lws-serve ./lws-store --port 3040
http://127.0.0.1:3040

$ curl -si -X PUT http://127.0.0.1:3040/notes/a.ttl -H "Content-Type: text/turtle" \
    --data '<#it> <http://purl.org/dc/terms/title> "A" .'
HTTP/1.1 201 Created
location: /notes/a.ttl
last-modified: Tue, 20 Oct 2026 22:08:49 GMT

$ curl -si http://127.0.0.1:3040/notes/a.ttl
HTTP/1.1 200 OK
content-type: text/turtle
last-modified: Tue, 20 Oct 2026 22:08:49 GMT
allow: GET, HEAD, OPTIONS, PUT, PATCH, DELETE
accept-patch: text/n3
link: <http://www.w3.org/ns/ldp#RDFSource>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type",
  </notes/a.ttl.acl>; rel="acl", </notes/a.ttl.meta>; rel="describedby",
  <http://127.0.0.1:3040/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription"

<#it> <http://purl.org/dc/terms/title> "A" .
```

### One process per storage directory

One process writes a storage directory
(<https://github.com/danbri/factoidal/issues/1135>). `lws-serve DIR`,
`solid-serve DIR` and each `webdav-serve` local mount hold the lock file
`DIR/lws.lock` while they run. The file holds the process id, the command,
the start time, the host name and a random token of the process. A clean
exit (Ctrl-C, SIGTERM, the end of the process) removes it.

- A start on a directory whose lock names a process that runs is refused.
  The message names the lock file and that process. Stop that process first:

  ```
  factoidal lws-serve: the storage directory /home/me/clear-store is in use: /home/me/clear-store/lws.lock
    names process 27083 (lws-serve, started 2026-10-28T08:48:29.823Z) on host vm, and that process runs.
    One process writes a storage directory (https://github.com/danbri/factoidal/issues/1135).
    Stop that process first.
  ```
- A lock of a process that does not run (for example after a crash) is
  taken over. The server prints a warning.
- A lock of another host is refused: this host cannot tell if that process
  runs. Remove the file only if it does not.
- A program that does not take the lock (another tool, an older Factoidal)
  is not stopped by it.

The engine decides the file, its contents and every refusal
([`LWS/DirLock.lean`](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/LWS/DirLock.lean));
the server only creates the file (`O_EXCL`), asks the system if a process
runs, and removes the file.

### Encryption at rest

Encryption at rest is off by default. Without a key, the storage is written
to disk in clear text, and every start says so on standard error:

```
lws-serve: encryption at rest is OFF: the storage in /home/me/clear-store is written to disk in clear text.
  To seal it, make a key with `factoidal lws-keygen`, keep a copy of the key in a safe place (a lost key
  is lost data), and start with FACTOIDAL_LWS_KEY set to it on an empty storage directory.
  See https://danbri.github.io/factoidal/web/hub/servers/#encryption-at-rest
```

To turn it on:

1. Make a key. `factoidal lws-keygen` prints 32 random bytes as 64 hex
   digits, and the key id on standard error.
2. Keep a copy of the key in a safe place. **If you lose the key, you lose
   the data.** There is no recovery.
3. Set `FACTOIDAL_LWS_KEY` to the key and start the server on an empty
   storage directory:

```
$ export FACTOIDAL_LWS_KEY="$(factoidal lws-keygen)"
factoidal lws-keygen: WARNING: EXPERIMENTAL UNREVIEWED CODE - ...
lws-keygen: key id fc5e47ded8ec8264. Keep a copy of the key in a safe place: without it the storage cannot be read.
lws-keygen: start the server with FACTOIDAL_LWS_KEY set to it, on an empty storage directory.
$ factoidal lws-serve ./lws-store --issuer https://issuer.example
factoidal lws-serve: WARNING: EXPERIMENTAL UNREVIEWED CODE - ...
lws-serve: encryption at rest is ON: the storage in /home/me/lws-store is sealed with ChaCha20-Poly1305
  under key id fc5e47ded8ec8264.
```

(Recorded 2026-10-28; the lines are wrapped here, and the directory
names are shortened.)

The same variable applies to `solid-serve DIR` and to `webdav-serve` local
mounts.

What is sealed (ChaCha20-Poly1305 from HACL\*, a new random nonce for every
write, authenticated before any byte is used):

- the snapshot `DIR/lws-state.json` (default mode): the whole storage;
- with `--storage files`: every body file `DIR/bodies/XX/N`, every journal
  record of `DIR/lws-journal`, and the metadata file `DIR/lws-files.json`.

What is not protected:

- the names of the files, their sizes and the times of the writes. In files
  mode a body file name is a number and holds no part of the resource path,
  but the number of body files and the size of each are visible;
- the lock file `DIR/lws.lock` (process id, command, start time, host name);
- the storage while the server runs: it is in the server's memory in clear
  text, and the answers go out as the protocol says;
- the key itself, in the environment of the server process.

Rules the engine applies at start: a wrong key, a changed or truncated file,
a clear-text storage with a key set, and a sealed storage without the key
each stop the start with a message.

Not possible yet (<https://github.com/danbri/factoidal/issues/1136>): to
change the key of a sealed storage, and to seal an existing clear-text
storage. Turn encryption on for a new, empty storage directory.

Design: [`LWS/SnapshotSeal.lean`](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/LWS/SnapshotSeal.lean),
[`LWS/FileLayout.lean`](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/LWS/FileLayout.lean),
<https://github.com/danbri/factoidal/issues/921>.

## Authorization server (OAuth 2.0 token exchange)

```
factoidal authz-serve DIR --resource IRI[,IRI...] [--issuer IRI] [--saml-idp FILE]...
```

What it does: the authorization server of the LWS 1.0 drafts, as a component
that any resource server can use. It serves RFC 8414 metadata, a JWK Set, and
an RFC 8693 token endpoint that exchanges a subject token for an RFC 9068
access token. It accepts three kinds of subject token:

- OpenID Connect ID tokens (lws10-authn-openid);
- self-issued CID credentials for `https` and `did:key` subjects
  (lws10-authn-ssi-cid);
- signed SAML 2.0 assertions from the identity providers that `--saml-idp`
  names (lws10-authn-saml).

A SAML assertion must carry one enveloped XML Signature in the SAML Core §5
profile (Exclusive XML Canonicalization 1.0, rsa-sha256), and it must verify
under the key in the configuration. The server never reads a key from the
assertion. Documents with a DTD, comments or a second signature are refused,
and so are wrapped assertions. `lws-serve --authz DIR` serves the
authorization server and the storage on one port.

`idp.json` is `{"entityId": "<the saml:Issuer value>", "jwk": <the RSA public
JWK>}`.

`--saml-decrypt-key key.json` (repeatable, a private JWK) lets the server
decrypt a `saml:EncryptedAssertion` or `saml:EncryptedID` (XML Encryption 1.1:
RSA-OAEP, ECDH-ES or AES Key Wrap for the key, AES-GCM for the content). The
decrypted assertion must carry its own valid signature. RSA and ECDH run in
the wasm (HACL\*); AES runs in the host's WebCrypto. Without the option,
encrypted assertions are refused. `saml:EncryptedAttribute` is refused:
<https://github.com/danbri/factoidal/issues/1073>.

Touchstone, `--config auth --authz factoidal`, 2026-10-27: auth/saml 3 pass,
0 fail (out of 3); auth/oidc 6 pass, 0 fail (out of 6); auth/cid 22 pass,
0 fail (out of 22). Record:
[docs/designissues/2026-10-27-saml-xml-signature.md](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-10-27-saml-xml-signature.md).

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
