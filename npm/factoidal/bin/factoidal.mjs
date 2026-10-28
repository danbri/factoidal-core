#!/usr/bin/env node
// The `factoidal` command: pack, activate, query, update and compact a
// persisted Shardborough store from Node or Deno, with no native binary.
// https://github.com/danbri/factoidal/issues/641
//
// STATE TODAY. The argument surface below is complete and settled, so that
// wiring the remaining subcommands changes no user-visible syntax.
// `version`, `inspect` and `query` run: the first needs only host file
// I/O, and the other two drive the three WebAssembly store operations of
// `formal/lean4/Wasm/Ops/Store.lean`. `pack`, `activate`, `update` and
// `compact` parse their arguments, report what they would do, and exit 3;
// they need operations that do not exist yet.
//
// This file reads files by name, moves bytes and renders what the engine
// answered. It parses no manifest, verifies no digest, decodes no block
// and chooses no artifact -- every one of those is a format decision and
// it lives in the Lean source (iron rule 7). The table renderer is a
// human display of the engine's own SPARQL Query Results JSON, not a
// second serializer: `--format json`, `--format nquads` and
// `--format turtle` all print documents the engine produced.

import {
  StoreHostError, atomicReplace, listGeneration, makeDirectory, readChunk, readWhole,
  runtime
} from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'
import { hexOfBytes, loadEngine } from './engine.mjs'
import { PackError, packSupported, verifyGeneration } from './pack.mjs'
import { denoReexec, isStackOverflow, runPack } from './pack-host.mjs'
import { SAMPLE_TURTLE, sampleStoreFacts } from '../sample-store.mjs'
import {
  planQueryOnWorker, queryStoreOnWorker, workerRouteAvailable
} from './store-worker-host.mjs'
import {
  STACK_REMEDY, StoreOperationError, inspectManifest, openStore, planQuery,
  queryStore, stackLimitAdvice, turtleOfNQuads
} from './store.mjs'
import { sbm11Api, setDefaultSbm11Reader } from '../lib/sbm11.mjs'
import { nodeDefaultReaderFactory } from '../lib/sbm11-node.mjs'

const EXIT_OK = 0
const EXIT_FAILURE = 1
const EXIT_USAGE = 2
const EXIT_NOT_WIRED = 3

// Progress is reported about every 16 MiB; the packer feeds 65,536 bytes
// a time, so this is the window that catches one feed per report.
const FEED_PROGRESS = 65536

const PACK_LAYOUTS = ['ibk3', 'ibk4', 'ibk5', 'sbm11']
// https://github.com/danbri/factoidal/issues/1009: an SBM11 generation is
// packed by the wasm op sbm11PackFiles, verified by sbm11Verify and queried
// by sbm11Open / sbm11Query (formal/lean4/Wasm/Ops/Sbm11*.lean). The op
// storeLayout says which store a directory holds; this file does not decide
// it from file names (iron rule 7).
// The syntaxes the packer reads and the file-name suffixes of each are the
// engine's tables (op engineTables: packSyntaxes, packSuffixes,
// packUnsupportedSuffixes), https://github.com/danbri/factoidal/issues/894.

/** The parent of a path, and its last component. The `activate` hint
 *  printed after a pack needs both; neither is a format decision. */
function dirOf (path) {
  const cut = path.replace(/[/\\]+$/, '').lastIndexOf('/')
  return cut <= 0 ? '.' : path.slice(0, cut)
}
function nameOf (path) {
  const trimmed = path.replace(/[/\\]+$/, '')
  const cut = trimmed.lastIndexOf('/')
  return cut < 0 ? trimmed : trimmed.slice(cut + 1)
}

const ISSUE = 'https://github.com/danbri/factoidal/issues/641'

const isDeno = typeof globalThis.Deno !== 'undefined'
const argv = isDeno ? globalThis.Deno.args.slice() : process.argv.slice(2)

// Node writes to a PIPE asynchronously, and `process.exit()` drops
// whatever is still buffered. A SELECT that prints a few megabytes of
// SPARQL Query Results JSON into `| jq` therefore arrived truncated at
// the 64 KiB pipe boundary (measured 2026-09-03, 6455 rows). Setting the
// exit code and letting the process end on its own flushes it.
function exit (code) {
  if (isDeno) globalThis.Deno.exit(code)
  else process.exitCode = code
}

let outSilenced = false
function out (line) { if (!outSilenced) console.log(line) }
function err (line) { console.error(line) }

// ---------------------------------------------------------------- usage

// Owner, 2026-10-27: every protocol, authentication and security component,
// the CLIs and the core library carry this notice. It is printed with every
// help text and on standard error when a server, client or key command starts.
const REVIEW_WARNING = 'EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.'

/** The commands that serve, speak a protocol, or handle keys and tokens. */
const WARNED_COMMANDS = new Set(['serve', 'lws-serve', 'solid-serve', 'solid-client', 'lws-client',
  'authz-serve', 'authz-keys', 'xmpp-serve', 'webdav-serve', 'webdav-user', 'xmpp-http-proxy', 'lws-keygen'])

const USAGE = `factoidal - the Factoidal persisted store, from Node or Deno

usage: factoidal <command> [options]

commands:
  version                     print the package and engine versions
  sample-store [DIR]          pack a small built-in store and print its path
  inspect  STORE              report what the activated manifest commits
  query    STORE [QUERY]      evaluate a SPARQL query against a store
  pack     INPUT OUTPUT       build one immutable generation from an RDF file
  activate STORE GENERATION   make one generation the activated generation
  update   STORE [UPDATE]     apply a SPARQL Update through the delta log
  compact  STORE GENERATION   fold the delta log into a new generation
  serve    STORE              serve SPARQL 1.1 Protocol, Graph Store and
                              Service Description over HTTP
  lws-serve DIR               serve Linked Web Storage 1.0 over HTTP
  solid-serve DIR             serve the Solid Protocol over HTTP
  lws-keygen                  print a new storage key for encryption at rest
                              (FACTOIDAL_LWS_KEY of lws-serve, solid-serve and
                              webdav-serve local mounts)
  solid-client OP URL         run one Solid client operation
  lws-client OP URL           run one Linked Web Storage client operation
  authz-serve DIR             serve an OAuth 2.0 authorization server for LWS
                              (RFC 8414 metadata, JWK Set, RFC 8693 token exchange)
  authz-keys DIR              print the public JWK Set of an authorization server
  xmpp-serve DIR              serve XMPP (RFC 6120/6121) over TCP or direct TLS
  webdav-serve CONFIGDIR      serve local and remote LWS storages to file
                              browsers over WebDAV (RFC 4918)
  webdav-user FILE NAME       add or replace a user in a webdav-serve users
                              file (the password is read from standard input)
  xmpp-http-proxy             a local HTTP listener (127.0.0.1) whose requests
                              go over XMPP (XEP-0332) to one target JID

global options:
  -h, --help                  print this text, or a command's own help
      --json                  machine-readable output where a command has it
      --quiet                 print results only, no progress lines

exit codes:
  0 success   1 failure   2 usage error   3 not yet wired (${ISSUE})

STORE is a collection root: the directory that holds CURRENT. Make one from
an RDF file with pack and activate, or try a small built-in one:

  factoidal query "$(factoidal sample-store)" 'SELECT * WHERE { ?s ?p ?o } LIMIT 5'`

const COMMAND_USAGE = {
  'sample-store': `factoidal sample-store - pack a small built-in store, print its path

usage: factoidal sample-store [DIR] [--json]

Packs the few triples held in sample-store.mjs (no data file ships) into a
store under DIR, or under the OS temporary directory, activates it, and
prints the collection root. A DIR that already holds CURRENT is reused.

  factoidal query "$(factoidal sample-store)" \\
    'SELECT ?c ?l WHERE { ?c <http://www.w3.org/2004/02/skos/core#prefLabel> ?l }'`,

  version: `factoidal version - print the package and engine versions

usage: factoidal version [--json]

Prints the npm package version, the Lean engine's WebAssembly digest as
recorded by its build, and which host-I/O implementation is loaded.`,


  inspect: `factoidal inspect - report what a store's manifest commits

usage: factoidal inspect STORE [--json] [--generation NAME]

Reads CURRENT, hands the manifest bytes to the engine's
storeManifestInspect operation, and prints what it decoded: the wire
version, the layout, the blank-node publication profile, the term-registry
version, whether the manifest carries a fixed-chunk Merkle commitment, and
one row per entry with its predicate, row count, byte length, block kind
and graph set.

options:
  --generation NAME  inspect this generation instead of the activated one
  --json             print the operation's envelope unchanged`,

  query: `factoidal query - evaluate a SPARQL query against a store

usage: factoidal query STORE [QUERY] [options]

QUERY is the query text. Give it as the second argument, or with --query,
or in a file with --file.

The command reads CURRENT and the manifest, asks the engine which
artifacts the query needs, reads exactly those, and hands their bytes to
the engine's storeQuery operation. The engine verifies every artifact
against the SHA-256 the manifest commits before it answers.

options:
  --query TEXT       the query text
  --file PATH        read the query text from a file
  --format FORMAT    table (default), json, nquads, turtle
  --limit N          print at most N table rows; the total is always named
  --explain          print the artifact plan instead of the results
  --generation NAME  query this generation instead of the activated one
  --json             shorthand for --format json
  --quiet            print the result only, no plan line on stderr
  --no-worker        never retry on a worker thread (see below)

Several engine paths recurse once per manifest entry or once per row, and
against a large collection that exceeds the runtime's default call stack.
A one-shot query builds no store handle, so it runs IN PROCESS and pays
nothing for a worker it would drop; only when the runtime runs out of
frames does it run again on a worker thread with a raised stack, or under
Deno re-execute itself once with a raised V8 stack, which needs
--allow-run and --allow-env (https://github.com/danbri/factoidal/issues/653).
--no-worker turns the retry off, and the frame budget is then reported.

A process that asks MANY questions about one store should hold a store
handle instead: openStoreHandleOnWorker in bin/store-worker-host.mjs
verifies and decodes once, on a thread with the raised stack, and answers
every later query from what it retained.

formats:
  table    a human display of the engine's SPARQL Query Results JSON;
           ASK prints true or false, CONSTRUCT and DESCRIBE print their
           N-Triples
  json     SELECT prints the engine's SPARQL 1.1 Query Results JSON
           document; ASK, CONSTRUCT and DESCRIBE print the operation's
           envelope, because the operation answers those with a boolean
           or a serialized graph rather than with a results document
  nquads   CONSTRUCT and DESCRIBE only: the graph the engine serialized
  turtle   CONSTRUCT and DESCRIBE only: that graph through the engine's
           own Turtle writer, which flattens named graphs into the default
           graph

not available, and why:
  --base IRI         the store query operation takes no base argument;
                     put a BASE clause in the query text instead
  xml, csv, tsv      the engine has no operation that writes the SPARQL
                     Results XML, CSV or TSV documents, and writing one
                     here would be a second serializer (iron rule 7)

A store carrying a non-empty delta log is not served by this path: the
operation reads the manifest's committed artifacts only. Use the native
l4block-* tools for a store with uncompacted updates.`,

  pack: `factoidal pack - build one immutable generation from an RDF file

usage: factoidal pack INPUT OUTPUT [options]

INPUT is an RDF file. OUTPUT is the generation directory to create; it is
normally STORE/gen-N. Packing does not activate: run activate next.

options:
  --layout LAYOUT    ibk5 (quads, wire version 10: RDF 1.2 terms,
                     out-of-line literals, zone maps; default), ibk4
                     (quads, wire version 9), ibk3 (triples) or sbm11
                     (the files l4sbm11-pack writes; the document is read
                     whole, in memory; serve does not read it yet)
  --syntax SYNTAX    turtle, trig or nquads, and with sbm11 also rdfxml or
                     jsonld; default from the file extension
  --chunk-bytes N    Merkle chunk size; default is the engine's
  --batch-bytes N    ibk4 only: source bytes between publication batches;
                     default is the engine's. Blocks are published during
                     the ingest pass, so this bounds the packer's memory.
                     Match l4block-shard-pack --batch-bytes for its blocks.
  --json             emit one JSON object
  --no-worker        pack in this process instead of on a worker thread

The pack fold recurses deeper than either runtime's default call stack
allows, so it runs on a worker thread with a raised stack under Node, and
under Deno the command re-executes itself once with a raised V8 stack
(https://github.com/danbri/factoidal/issues/649). --no-worker turns both
off; a pack above about half a megabyte of input then overflows.`,

  activate: `factoidal activate - make one generation the activated generation

usage: factoidal activate STORE GENERATION [--json]

Verifies every artifact of GENERATION and every cross-artifact relation,
then atomically replaces STORE/CURRENT. A generation that fails
verification never becomes current. For an SBM11 generation the engine
checks the length, SHA-256 and Merkle root of every file and every
.merkle sidecar against the manifest (op sbm11Verify); it does not run
the decoder checks of l4sbm11 activate.`,

  update: `factoidal update - apply a SPARQL Update through the delta log

usage: factoidal update STORE [UPDATE] [options]

UPDATE is the update text. Give it as the second argument, or with
--update, or in a file with --file. The batch is appended to the
activated generation's delta log and is visible to the next query.

options:
  --update TEXT      the update text
  --file PATH        read the update text from a file
  --json             emit one JSON object`,

  compact: `factoidal compact - fold the delta log into a new generation

usage: factoidal compact STORE GENERATION [options]

Reads the activated generation and its committed delta batches, writes
GENERATION as a new immutable generation under STORE, and records its
compacted epoch. It does not activate unless --activate is given.

options:
  --activate         activate the new generation when it verifies
  --json             emit one JSON object`,

  serve: `factoidal serve - a SPARQL 1.1 endpoint over an activated store

usage: factoidal serve STORE [--port N] [--host ADDRESS] [options]
       factoidal serve --file DATA /DATASET [--port N] [options]
       factoidal serve --tdb2 DIR /DATASET [--port N] [options]

The second form matches fuseki-server --file DATA /DATASET: DATA is packed
into a temporary collection (layout ibk5 unless --layout is given), served
at /DATASET/sparql (also /DATASET/query and /DATASET/update) and
/DATASET/data (also /DATASET/get, read only). Updates are lost on exit.

The third form matches fuseki-server --loc DIR /DATASET for an Apache Jena
TDB2 database: DIR is read in place, read only. SPARQL query and Graph Store
GET work; an update or a Graph Store write answers 501 with a message. The
current Data-NNNN generation is served; a database whose journal.jrnl is not
empty (Jena has not replayed it) is refused. The Lean decoder reads the
indexes and node table (formal/lean4/L4Factoidal/Tdb2/Read.lean); every
quad is held in memory while the server runs.

Serves the activated generation of STORE, with its delta log, over HTTP:

  GET/POST /sparql   SPARQL 1.1 Protocol query and update
                     (GET /sparql with no query string: the SPARQL 1.1
                     Service Description of the endpoint)
  /data, /data/...   SPARQL 1.1 Graph Store HTTP Protocol (?default,
                     ?graph=IRI, or a path under /data naming the graph)

options:
  --port N           the port to bind; 0 takes an ephemeral one (default 3030)
  --host ADDRESS     the address to bind (default 127.0.0.1)
  --query-path PATH  the query and update endpoint (default /sparql)
  --gsp-path PATH    the Graph Store endpoint (default /data)
  --file DATA        pack and serve an RDF file (see the second form)
  --tdb2 DIR         serve a Jena TDB2 database read only (third form)
  --layout LAYOUT    with --file: ibk3, ibk4 or ibk5 (default ibk5)
  --no-worker        serve on this thread instead of a worker thread with a
                     raised call stack (large collections need the worker)
  --quiet            print the origin only
  --allow-host NAME
                     also answer requests whose Host field names NAME (a reverse
                     proxy or a Tailscale name); give it once per name, with no
                     port. Without it the listener answers only localhost,
                     127.0.0.1, [::1], the --host address and the addresses of
                     its interfaces, and gives 421 Misdirected Request to any
                     other Host (DNS rebinding)
  --allow-origin ORIGIN
                     also accept a request that changes state (any method but
                     GET, HEAD and OPTIONS) from this origin, written
                     scheme://host[:port]; give it once per origin. Without it
                     such a request with an Origin field of another origin gets
                     403 (a cross-site form POST)
                     https://github.com/danbri/factoidal/issues/1124

serve has no authentication: anyone who reaches the port can query and
update the store. The Host and Origin checks above stop a web page in the
user's browser from doing so (formal/lean4/L4Factoidal/HTTP/LocalGuard.lean).

An update, or a Graph Store PUT, POST or DELETE, is appended to the
activated generation's delta log as one batch before the response is sent,
and is visible to the next request. An IBK3 (triples) generation accepts
changes to the default graph only, because its delta log is replayed and
compacted for that graph only; a change to a named graph answers 501. A
quad generation (ibk4, ibk5, the default) accepts every graph. Fold the log into a new
generation with l4block-shard-compact, activate it, and restart the server.

The server makes no protocol decision: the request framing, routing,
status codes, content negotiation, evaluation and the delta-log batch are
decided by formal/lean4/L4Factoidal/HTTP/Wire.lean and
formal/lean4/L4Factoidal/SPARQL/StoreEndpoint.lean through the
storeServe operations. A WebAssembly module built before those operations
landed makes this command exit 3 and say so.

Specifications: https://www.w3.org/TR/sparql11-protocol/
https://www.w3.org/TR/sparql11-http-rdf-update/
https://www.w3.org/TR/sparql11-service-description/`,

  'authz-serve': `factoidal authz-serve - serve an OAuth 2.0 authorization server

usage: factoidal authz-serve DIR --resource IRI[,IRI...] [--issuer IRI]
                           [--port N] [--host ADDRESS] [--alg ES256|EdDSA]
                           [--token-lifetime SECONDS] [--rotate-after SECONDS]
                           [--allow-http] [--allow-private-fetch]
                           [--cors-origin ORIGIN]... [--no-cors]
                           [--saml-idp FILE]... [--saml-decrypt-key FILE]...

An authorization server as a component (https://github.com/danbri/factoidal/issues/916),
for lws-serve and any resource server that reads RFC 8414 metadata:
  GET  /.well-known/lws-configuration (also /.well-known/oauth-authorization-server)
  GET  /jwks                          the JWK Set (public keys only)
  POST /token                         RFC 8693 token exchange for an RFC 9068
                                      access token whose aud is the resource
Subject tokens: OpenID Connect ID tokens (lws10-authn-openid) and
self-issued JWTs for https and did:key subjects (lws10-authn-ssi-cid), and
SAML 2.0 assertions (lws10-authn-saml) from the identity providers --saml-idp
names (https://github.com/danbri/factoidal/issues/926).

--saml-idp FILE (repeatable) trusts one SAML 2.0 identity provider. FILE is
JSON: {"entityId": "<the saml:Issuer value>", "jwk": <its RSA public JWK>}.
An assertion must carry one enveloped XML Signature (exclusive
canonicalization, rsa-sha256) that verifies under that key, an audience that
names the issuer of this server, and bearer subject confirmation; its NameID
is the subject and its Recipient the client. Without --saml-idp the token
type is refused and not advertised.

--saml-decrypt-key FILE (repeatable) is one private JWK (RSA, EC P-256, OKP
X25519 or oct) that decrypts saml:EncryptedAssertion and saml:EncryptedID
(XML Encryption 1.1: RSA-OAEP, ECDH-ES with AES Key Wrap, or AES Key Wrap;
content AES-GCM). AES runs through WebCrypto. The decrypted assertion must
be signed as above. Without it, encrypted assertions are refused
(https://github.com/danbri/factoidal/issues/1073).

--resource names the resource IRIs (for lws-serve: BASE.well-known/lws-storage)
tokens may be issued for; any other is refused with invalid_target.
--issuer defaults to the bound origin. Give lws-serve --issuer the same IRI.
DIR holds the signing keys (DIR/authz-keys.json, mode 0600), sealed with
FACTOIDAL_LWS_KEY when it is set. --rotate-after makes a new key when the
current one is that old; the old key stays published until its tokens expire.
--allow-http accepts http subject identifiers; --allow-private-fetch lets the
server fetch documents from loopback, link-local and private addresses. Both
are off by default and are for tests.
CORS (https://github.com/danbri/factoidal/issues/923): by default every answer
echoes a valid request Origin in Access-Control-Allow-Origin, so a page on
another origin can read the metadata and keys and exchange a token; a
preflight is answered 204 first. --cors-origin ORIGIN (repeatable) answers
only those origins; --no-cors sends no CORS fields.

Every decision is made in formal/lean4/L4Factoidal/Authz/; this command only
carries sockets, the clock, random bytes, DNS answers and files.`,

  'authz-keys': `factoidal authz-keys - print the JWK Set of an authorization server

usage: factoidal authz-keys DIR [--private]

Prints the published JWK Set of the key file in DIR. --private prints the
private keys (with d): for a conformance harness that mints test tokens
(tools/lws-touchstone.sh --authz factoidal). Never publish that output.`,

  'lws-serve': `factoidal lws-serve - serve Linked Web Storage 1.0 over HTTP

usage: factoidal lws-serve DIR (--authz DIR | --issuer IRI | --auth-config FILE | --insecure-no-auth)
                         [--owner WEBID] [--root-acl FILE] [--audience IRI]
                         [--alg ES256|EdDSA] [--token-lifetime SECONDS] [--rotate-after SECONDS]
                         [--allow-http] [--allow-private-fetch]
                         [--port N] [--host ADDRESS] [--base IRI] [--page-size N]
                         [--paginate-always] [--moves all|data|off]
                         [--no-linkset-put] [--unstable-search-results] [--merkle]
                         [--controller-inbox URL] [--delivery-limit N]
                         [--delivery-window SECONDS] [--redirects-max N]
                         [--storage snapshot|files]
                         [--cors-origin ORIGIN]... [--no-cors]

Starts a Node HTTP server that answers every request through the engine's
lwsStep operation.

DIR names the storage directory. The storage is kept in the engine
handle and written to DIR/lws-state.json after every request that
changed it (temporary file, fsync, rename), and read back on the next
start. The engine decides the snapshot format and refuses a snapshot
path with a dot segment or other traversal form
(formal/lean4/L4Factoidal/LWS/Snapshot.lean).

With --storage files (off by default) a write costs the same whatever the
size of the storage: DIR holds one file per resource body (DIR/bodies/),
a journal of metadata changes (DIR/lws-journal) and a metadata file
(DIR/lws-files.json) that the journal is folded into from time to time.
A journal record is valid only when it is complete and its SHA-256
matches; a torn last record is ignored at start. An existing
DIR/lws-state.json is migrated at the first start and renamed to
lws-state.json.migrated. The engine decides every file name and every
byte (formal/lean4/L4Factoidal/LWS/FileLayout.lean); the storage is still
held in memory while the server runs
(docs/designissues/2026-10-22-lws-storage-on-disk.md).

Encryption at rest (off by default): when the environment variable
FACTOIDAL_LWS_KEY holds a 32-byte key (64 hex digits, or 43 characters of
base64url), the snapshot is sealed with ChaCha20-Poly1305 (HACL*) under a
new random nonce for every write, and authenticated when the storage is
opened. A wrong key, a changed or truncated file, a clear-text file with the
variable set, or a sealed file without it stops the start with a message.
It protects the file on disk only (formal/lean4/L4Factoidal/LWS/SnapshotSeal.lean).
Make a key with \`factoidal lws-keygen\`; keep a copy, a lost key is lost data.
At start the server says on standard error whether the storage is sealed
(and the key id) or written in clear text.

One process writes DIR (https://github.com/danbri/factoidal/issues/1135):
the server holds the lock file DIR/lws.lock while it runs and removes it at
a clean exit. A start refuses a DIR whose lock names a process that runs
(another lws-serve, solid-serve or webdav-serve local mount). A lock left by
a process that does not run (after a crash) is taken over with a warning.
The engine decides the file, its contents and every refusal
(formal/lean4/L4Factoidal/LWS/DirLock.lean).

  --port N        the port to bind; 0 takes an ephemeral one (default 3000)
  --host ADDRESS  the address to bind (default 127.0.0.1)
  --base IRI      the absolute IRI the storage root maps to
                  (default: the bound origin)
  --page-size N   the engine's container page size (config member pageSize;
                  default 100, 0 turns pagination off)
  --paginate-always
                  present every container listing as paginated, also one
                  that fits on one page (config member paginateAlways;
                  default off): rel="first" and rel="last", no rel="next"
  --moves all|data|off
                  which resources a client may move by changing their up
                  link (config member moves; default all): data resources
                  and containers, data resources only (the MoveResource
                  capability's appliesTo is [DataResource]), or none (no
                  MoveResource capability; a change of up answers 409)
  --no-linkset-put
                  a linkset resource does not accept PUT (config member
                  linksetPut false): its Allow leaves PUT out and a PUT
                  answers 405 Method Not Allowed; PATCH still applies
  --unstable-search-results
                  ANTICIPATORY AND UNSTABLE, off by default: a QUERY answer
                  of the type search names a results resource with
                  Content-Location (RFC 10008 section 2.3). lws10-index
                  defines no such resource; this is likely to change.
                  https://github.com/danbri/factoidal/issues/922
  --merkle        off by default: keep a SHA-256 digest of every resource
                  and a Merkle root of every container, and show them: an
                  RFC 9530 Repr-Digest field on GET of a resource, a
                  Factoidal-Merkle-Root field and listing member on a
                  container, and the storage root's digest in the storage
                  description (roots to the storage controller only under
                  authorization). Entity tags do not change. The hashes are
                  rebuilt when the storage is opened, not stored.
                  https://github.com/danbri/factoidal/issues/919
  --controller-inbox URL
                  the storage controller's inbox (config member
                  controllerInbox; default none): each new access request
                  is announced there with a Create notification. The LWS
                  draft names no such inbox; this is a server choice.
                  https://github.com/danbri/factoidal/issues/920
  --delivery-limit N
                  the most webhook deliveries one subscription gets in one
                  window (config member deliveryLimit; default 10, 0 turns
                  the limit off); the changes over it wait and go in one
                  batched notification when the window ends
                  https://github.com/danbri/factoidal/issues/915
  --delivery-window SECONDS
                  the length of that window (config member deliveryWindow;
                  default 60)
  --redirects-max N
                  the most previous identifiers of moved resources kept to
                  answer 301 Moved Permanently (config member redirectsMax;
                  default 256)
                  https://github.com/danbri/factoidal/issues/914
  --storage snapshot|files
                  how DIR keeps the storage (config member storage;
                  default the environment variable FACTOIDAL_LWS_STORAGE,
                  else snapshot): one snapshot file written whole after
                  each change, or one file per body with a journal, so a
                  write costs the same whatever the storage size
                  https://github.com/danbri/factoidal/issues/918
  --cors-origin ORIGIN
                  answer CORS (Fetch Standard) only for this origin, written
                  scheme://host[:port] (for example https://danbri.github.io);
                  give it once per origin. Default under authorization: echo
                  any valid request Origin, as the Solid Protocol section 8.1
                  requires of Solid servers. Default with --insecure-no-auth:
                  no CORS fields, because every request is served there and an
                  echo would let any web page read and write the storage
                  (https://github.com/danbri/factoidal/issues/1124). Never
                  Access-Control-Allow-Credentials: the token
                  travels in Authorization. A preflight (OPTIONS with
                  Access-Control-Request-Method) is answered 204 before any
                  authorization decision.
                  https://github.com/danbri/factoidal/issues/923
  --no-cors       send no CORS fields; a page on another origin cannot read
                  any answer

Authorization (LWS editor's draft, section Authorization; one of the four
is required):
  --authz DIR           also serve an authorization server on this port, its
                        issuer the storage root without the trailing slash
                        (BASE less "/"): RFC 8414 metadata at
                        /.well-known/lws-configuration, the token endpoint at
                        BASE.well-known/lws-token, the JWK Set at
                        BASE.well-known/lws-jwks, signing keys in DIR (as
                        authz-serve; --alg, --token-lifetime, --rotate-after,
                        --allow-http, --allow-private-fetch, --saml-idp and
                        --saml-decrypt-key as there). The
                        storage trusts it, and any --issuer too. Each request
                        is the authorization server's when the engine says so
                        (L4Factoidal/Authz/Mount.lean); every other is the
                        storage's. A proxy may serve BASE at a path prefix and
                        remove the prefix: both forms of every path are read.
  --issuer IRI          trust this authorization server; several may be
                        given separated by commas. Its metadata is read from
                        IRI/.well-known/lws-configuration and its keys from
                        the jwks_uri there, when a token first needs them.
  --auth-config FILE    the engine's "auth" configuration as JSON:
                        {"issuers":[{"issuer":IRI,"jwks":{...}?}],
                         "audience":IRI?, "leeway":SECONDS?,
                         "refreshInterval":SECONDS?}
  --insecure-no-auth    development only: no authorization at all; every
                        request is served. Never the default. The storage
                        then answers only its own host names and refuses
                        writes from other origins (see --allow-host and
                        --allow-origin), and sends no CORS fields unless
                        --cors-origin names an origin.
  --allow-host NAME     with --insecure-no-auth:
                        also answer requests whose Host field names NAME (a reverse
                        proxy or a Tailscale name); give it once per name, with no
                        port. Without it the listener answers only localhost,
                        127.0.0.1, [::1], the --host address and the addresses of
                        its interfaces, and gives 421 Misdirected Request to any
                        other Host (DNS rebinding)
  --allow-origin ORIGIN with --insecure-no-auth:
                        also accept a request that changes state (any method but
                        GET, HEAD and OPTIONS) from this origin, written
                        scheme://host[:port]; give it once per origin. Without it
                        such a request with an Origin field of another origin gets
                        403 (a cross-site form POST)
                        https://github.com/danbri/factoidal/issues/1124
  --owner WEBID         the storage owner: a new storage gets a root ACL
                        that gives this agent Read, Write and Control
  --root-acl FILE       a Turtle root ACL for a new storage instead
  --audience IRI        the aud value tokens must carry (default: the
                        storage IRI, BASE.well-known/lws-storage, which
                        every lws#storage link names)

Requests carry an access token as "Authorization: Bearer TOKEN" (RFC 6750).
The engine verifies its JWS signature (ES256, RS256 or EdDSA, with the
vendored HACL* code), its iss, aud, exp, nbf and iat, and then decides
access with Web Access Control over the storage's ACL resources. A
request without a valid token answers 401 with
WWW-Authenticate: Bearer resource_metadata="..." (RFC 9728), and the
metadata document is served at /.well-known/oauth-protected-resource.

The server makes no protocol decision: status codes, Link relations,
Last-Modified, the PATCH blank-node refusal and every authorization
decision are answered by formal/lean4/L4Factoidal/LWS/. A WebAssembly module built before those
operations landed makes this command exit 3 and say so.

Specification: https://w3c.github.io/lws-protocol/lws10-core/`,

  'solid-serve': `factoidal solid-serve - serve the Solid Protocol over HTTP

usage: factoidal solid-serve DIR (--issuer IRI | --auth-config FILE | --insecure-no-auth)
                           [--owner WEBID] [--port N] [--host ADDRESS] [--base IRI]

Starts a Node HTTP server that answers every request through the engine's
solidStep operation.

DIR names the storage directory. The storage is kept in the engine
handle and written to DIR/lws-state.json after every request that
changed it (temporary file, fsync, rename), and read back on the next
start. The engine decides the snapshot format and refuses a snapshot
path with a dot segment or other traversal form
(formal/lean4/L4Factoidal/LWS/Snapshot.lean).

Encryption at rest (off by default): when the environment variable
FACTOIDAL_LWS_KEY holds a 32-byte key (64 hex digits, or 43 characters of
base64url), the snapshot is sealed with ChaCha20-Poly1305 (HACL*) under a
new random nonce for every write, and authenticated when the storage is
opened. A wrong key, a changed or truncated file, a clear-text file with the
variable set, or a sealed file without it stops the start with a message.
It protects the file on disk only (formal/lean4/L4Factoidal/LWS/SnapshotSeal.lean).
Make a key with \`factoidal lws-keygen\`; keep a copy, a lost key is lost data.
At start the server says on standard error whether the storage is sealed
(and the key id) or written in clear text.

One process writes DIR (https://github.com/danbri/factoidal/issues/1135):
the server holds the lock file DIR/lws.lock while it runs and removes it at
a clean exit. A start refuses a DIR whose lock names a process that runs
(another lws-serve, solid-serve or webdav-serve local mount). A lock left by
a process that does not run (after a crash) is taken over with a warning.
The engine decides the file, its contents and every refusal
(formal/lean4/L4Factoidal/LWS/DirLock.lean).

  --port N        the port to bind; 0 takes an ephemeral one (default 3000)
  --host ADDRESS  the address to bind (default 127.0.0.1)
  --base IRI      the absolute IRI the storage root maps to
                  (default: the bound origin)
  --owner WEBID   the WebID the storage advertises as its owner; under
                  authentication it gets acl:Read, acl:Write and
                  acl:Control on the root (Web Access Control §3.2)
  --issuer IRI    trust this Solid-OIDC issuer (comma separated for more).
                  The engine verifies each DPoP-bound access token
                  (Solid-OIDC §8, §9.3; RFC 9449): signature under the
                  issuer's keys found by OpenID Connect Discovery, aud
                  "solid", webid, exp, cnf.jkt bound to the DPoP key,
                  htm, htu, iat and a jti replay cache, and that the
                  WebID profile lists the issuer (solid:oidcIssuer).
  --auth-config FILE  the same as JSON: {"issuers":[{"issuer":IRI,
                  "jwks":{...}?}], "leeway"?, "iatWindow"?,
                  "refreshInterval"?, "checkProfileIssuer"?}
  --insecure-no-auth  development only: no authentication; Web Access
                  Control is not enforced. The server then answers only its
                  own host names and refuses writes from other origins.
  --allow-host NAME   with --insecure-no-auth:
                  also answer requests whose Host field names NAME (a reverse
                  proxy or a Tailscale name); give it once per name, with no
                  port. Without it the listener answers only localhost,
                  127.0.0.1, [::1], the --host address and the addresses of
                  its interfaces, and gives 421 Misdirected Request to any
                  other Host (DNS rebinding)
  --allow-origin ORIGIN  with --insecure-no-auth:
                  also accept a request that changes state (any method but
                  GET, HEAD and OPTIONS) from this origin, written
                  scheme://host[:port]; give it once per origin. Without it
                  such a request with an Origin field of another origin gets
                  403 (a cross-site form POST)
                  https://github.com/danbri/factoidal/issues/1124

The server makes no protocol decision. Storage discovery, containment
triples, slash semantics, the Allow and Accept-* headers, the PUT/POST/
PATCH/DELETE rules, the acl and describedby lifecycle, N3 Patch, Web
Access Control, CORS and the LDN inbox are answered by
formal/lean4/L4Factoidal/Solid/Server/. A WebAssembly module built before
those operations landed makes this command exit 3 and say so.

Specification: https://solidproject.org/TR/protocol`,

  'xmpp-serve': `factoidal xmpp-serve - serve XMPP (RFC 6120 and RFC 6121) over TCP or direct TLS

usage: factoidal xmpp-serve DIR [--domain NAME] [--port N] [--host ADDRESS]
                            [--accounts FILE] [--cert FILE --key FILE]

Starts a Node TCP server that runs one engine session per connection and
answers every byte through the engine's xmppSessionFeed operation.

DIR is the state directory, laid out as the native carrier's
(formal/lean4/Harness/XmppServe.lean): DIR/accounts holds one
user:password per line (unless --accounts names another file), rosters
are persisted under DIR/roster/, and a stanza written as a file under
DIR/spool/<bare jid>/ is delivered to that account's bound session.

  --domain NAME    the domain the server is authoritative for (default localhost);
                   a stream for any other domain is answered host-unknown
  --port N         the port to bind; 0 takes an ephemeral one
                   (default 5222, or 5223 with --cert and --key)
  --host ADDRESS   the address to bind (default 127.0.0.1)
  --accounts FILE  the accounts file (default DIR/accounts)
  --cert FILE      PEM certificate chain: XEP-0368 direct TLS, no STARTTLS
  --key FILE       PEM private key for --cert

The server makes no protocol decision. Stream negotiation, SASL PLAIN and
SCRAM-SHA-256, resource binding, the roster, presence subscription and
broadcast, message routing with the server-stamped from, stream errors and
disco#info are answered by formal/lean4/L4Factoidal/XMPP/. A WebAssembly
module built before the session operations landed makes this command
exit 3 and say so.

Not implemented: STARTTLS (use --cert/--key), server-to-server federation,
MUC/MIX/GC3 rooms.

Specifications: https://www.rfc-editor.org/rfc/rfc6120 and
https://www.rfc-editor.org/rfc/rfc6121`,

  'xmpp-http-proxy': `factoidal xmpp-http-proxy - reach an HTTP server over XMPP (XEP-0332) from 127.0.0.1

usage: factoidal xmpp-http-proxy --xmpp JID --xmpp-password-file FILE
                 --target JID/RESOURCE [--port N] [--host 127.0.0.1]
                 [--xmpp-host H] [--xmpp-port P] [--xmpp-tls] [--xmpp-ca FILE]
                 [--xmpp-resource R] [--timeout SECONDS]

Connects OUT to an XMPP server as JID (SASL SCRAM-SHA-256), binds a resource,
and opens an HTTP listener on 127.0.0.1. Every HTTP request to that listener
is sent as a XEP-0332 request to --target, and the answer is written back.
So a file browser, rclone, curl or "factoidal lws-client" uses
http://127.0.0.1:PORT/ to reach "factoidal webdav-serve CONFIGDIR --xmpp"
behind NAT. JID must be in that server's --xmpp-allow list, or every
request gets 403.

  --xmpp JID                 the account (user@domain[/resource])
  --xmpp-password-file FILE  the account's password (first line)
  --target JID/RESOURCE      the full JID of the server (as webdav-serve
                             --xmpp prints it). Requests go to this JID and
                             to no other: this is not an open proxy.
  --port N                   the port to listen on (default 8091; 0 takes an
                             ephemeral one)
  --host ADDRESS             the address to listen on: 127.0.0.1 only. Any
                             other address is refused (exit 1).
  --xmpp-host H              the XMPP server's address (default: the JID's
                             domain; no DNS SRV lookup)
  --xmpp-port P              default 5222, or 5223 with --xmpp-tls
  --xmpp-tls                 direct TLS (XEP-0368). Without it, only a
                             loopback --xmpp-host (127.0.0.0/8, ::1) is
                             accepted.
  --xmpp-ca FILE             PEM certificates to trust for --xmpp-tls
  --xmpp-resource R          the resource to bind (default proxy)
  --timeout SECONDS          how long a request waits for its answer
                             (default 60, 1 to 3600); then 504

It prints the listener's origin (http://127.0.0.1:PORT/) on standard output.

The listener has no login of its own. Every process on this computer that
can open a connection to 127.0.0.1 acts as JID, and a web page in a browser
on this computer can send requests to it (the Host and Origin check of
https://github.com/danbri/factoidal/issues/1124 is not in this command yet).
Authorization headers pass to the target unchanged; the proxy adds no
credential. Proxy-Authorization and the other hop-by-hop headers (RFC 9110
section 7.6.1) are not forwarded. A request body above 16 MiB gets 413, more
than 16 waiting requests 503, an absolute-form request target (a forward
proxy request) 400, CONNECT 405.

Every decision is in formal/lean4/L4Factoidal/XMPP/HttpRequester.lean and
formal/lean4/Wasm/Ops/XmppClient.lean. Design:
docs/designissues/2026-10-28-http-over-xmpp.md
(https://github.com/danbri/factoidal/issues/1107).`,

  'webdav-serve': `factoidal webdav-serve - serve LWS storages to file browsers over WebDAV

usage: factoidal webdav-serve CONFIGDIR [--port N] [--host ADDRESS]
                              [--users FILE] [--cert FILE --key FILE]
                              [--allow-host NAME]... [--allow-origin ORIGIN]...
                              [--login-limit N] [--login-window SECONDS]
                              [--dangerously-disable-ratelimits]
       factoidal webdav-serve CONFIGDIR --xmpp JID --xmpp-password-file FILE
                 --xmpp-allow JID[,JID...] [--xmpp-host H] [--xmpp-port P] [--xmpp-tls]

Starts a WebDAV server (RFC 4918, classes 1 and 2) that macOS Finder,
Windows Explorer, GNOME Files and KDE Dolphin can connect to. Its root
collection holds one folder per mount; a mount is one Markdown file
CONFIGDIR/NAME.md (README.md is not a mount):

    # Display name
    - kind: local | lws
    - path: ./alice-storage        (local: an lws-serve storage directory)
    - url: https://storage.example/alice/   (lws: the storage root)
    - auth: none | did-key | bearer
    - key-file: ./alice.jwk        (did-key: a P-256 private JWK; made when absent)
    - token-file: ./alice.token    (bearer: an access token)
    - writable: true | false       (default true for local, false for lws)
    - storage: snapshot | files    (local: default what the directory holds)
    - base: IRI                    (local: the storage root's IRI, default http://localhost/)

Only the first "# " heading and the first "- key: value" list are read; the
words in brackets above are notes, not part of a value. A malformed file
stops the start with its name and line number.

A local mount opens the directory with the operations lws-serve uses, as
the storage's owner. It takes the lock DIR/lws.lock as lws-serve does
(https://github.com/danbri/factoidal/issues/1135): a directory that
lws-serve, solid-serve or another webdav-serve holds stops the start with a
message that names the lock file and the process. At start each local mount
says whether its storage is sealed (FACTOIDAL_LWS_KEY, see lws-serve --help
and factoidal lws-keygen) or written in clear text. An lws mount reaches the
storage through the LWS client.

  --port N         the port to bind (default 8090; 0 takes an ephemeral one)
  --host ADDRESS   the address to bind (default 127.0.0.1)
  --users FILE     every request needs a user name and password (HTTP Basic,
                   RFC 7617) from FILE, made with "factoidal webdav-user";
                   without TLS only on a loopback address (127.0.0.1, ::1),
                   because Basic sends the password in clear text
  --cert FILE      a PEM certificate chain: serve HTTPS (TLS)
  --key FILE       the PEM private key of --cert
  --login-limit N  with --users: failed logins allowed per user name and per
                   client address in one window (default 5, 1 to 1000)
  --login-window SECONDS
                   with --users: the window of --login-limit (default 60,
                   1 to 86400)
  --dangerously-disable-ratelimits
                   with --users: no failed-login limit (a warning is printed
                   at start); any client can then try passwords without end
  --allow-host NAME
                   also answer requests whose Host field names NAME (a reverse
                   proxy or a Tailscale name); give it once per name, with no
                   port. Without it the listener answers only localhost,
                   127.0.0.1, [::1], the --host address and the addresses of
                   its interfaces, and gives 421 Misdirected Request to any
                   other Host (DNS rebinding)
  --allow-origin ORIGIN
                   also accept a request that changes state (any method but
                   GET, HEAD and OPTIONS) from this origin, written
                   scheme://host[:port]; give it once per origin. Without it
                   such a request with an Origin field of another origin gets
                   403 (a cross-site form POST)
                   https://github.com/danbri/factoidal/issues/1124

Without --users the listener has no login: anyone who can reach the port can
read and write every writable mount. Keep it on 127.0.0.1, or give --users
and --cert/--key. A users file holds PBKDF2-HMAC-SHA256 password hashes, one
user per line, NAME:pbkdf2-sha256:ITERATIONS:SALT_B64:HASH_B64; a malformed
line stops the start with the file name and line number. Expert review of the
login: https://github.com/danbri/factoidal/issues/1117

Failed logins are limited by default
(https://github.com/danbri/factoidal/issues/1119): after 5 failed logins in 60
seconds for one user name (known or not) or from one client address (an IPv6
client by its /64), a request with credentials gets 429 Too Many Requests
with Retry-After, and no password is checked, also the right one, until that
window ends. A request with no credentials is a 401 and does not count.

HTTP over XMPP (XEP-0332; https://github.com/danbri/factoidal/issues/1107):
with --xmpp the server opens NO port. It connects OUT to an XMPP server as
JID (SASL SCRAM-SHA-256), binds a resource, and answers XEP-0332 requests
from the bare JIDs in --xmpp-allow (others get "forbidden"). A server behind
NAT is reached this way with no inbound port.

  --xmpp JID                 the account (user@domain[/resource])
  --xmpp-password-file FILE  the account's password (first line)
  --xmpp-allow JID[,JID]     bare JIDs that may send requests (required)
  --xmpp-host H              the XMPP server's address (default: the JID's
                             domain; no DNS SRV lookup)
  --xmpp-port P              default 5222, or 5223 with --xmpp-tls
  --xmpp-tls                 direct TLS (XEP-0368); STARTTLS is not
                             implemented. Without it, only a loopback
                             --xmpp-host (127.0.0.0/8, ::1) is accepted.
  --xmpp-ca FILE             PEM certificates to trust for --xmpp-tls
  --dangerously-allow-writable-without-login
                             start although a local mount is writable:
                             there is no login on the XMPP path yet
                             (https://github.com/danbri/factoidal/issues/1125),
                             so every allowed JID writes as the owner.
                             Without it such a start is refused.
  --xmpp-resource R          the resource to bind (default dav)

It prints the bound JID (xmpp:user@domain/resource) on standard output.
XEP-0332 is Deferred, and no WebDAV client speaks it: a reader runs
"factoidal xmpp-http-proxy --target JID/RESOURCE" (as an allowed JID) and
points the file browser at the http://127.0.0.1:PORT/ that it prints.

Connect: macOS Finder, Go > Connect to Server, http://127.0.0.1:8090/ ;
Windows, Map network drive, http://127.0.0.1:8090/ ; GNOME Files,
dav://127.0.0.1:8090/ .

The server makes no protocol decision: every method, status, property, lock
and mapping is decided by formal/lean4/L4Factoidal/WebDAV/. A WebAssembly
module built before the WebDAV operations landed makes this command exit 3
and say so. Design: docs/designissues/2026-10-27-webdav.md
(https://github.com/danbri/factoidal/issues/1066).`,

  'lws-keygen': `factoidal lws-keygen - print a new storage key for encryption at rest

usage: factoidal lws-keygen [--json]

Prints a new 32-byte storage key as 64 hex digits on standard output, and its
key id (the first 8 bytes of SHA-256 of the key) on standard error. Set the
environment variable FACTOIDAL_LWS_KEY to it before lws-serve DIR,
solid-serve DIR or webdav-serve with a local mount, on an empty storage
directory:

  export FACTOIDAL_LWS_KEY="$(factoidal lws-keygen)"

Keep a copy of the key in a safe place. Without the key the storage cannot be
read: there is no recovery. Changing the key of an existing storage is not
possible (https://github.com/danbri/factoidal/issues/1136).
--json prints {"key": ..., "keyId": ...}.

The random bytes come from the host (WebCrypto getRandomValues); the engine
makes the key text and the key id (formal/lean4/L4Factoidal/LWS/DirLock.lean,
newStorageKey).`,

  'webdav-user': `factoidal webdav-user - add or replace a user in a webdav-serve users file

usage: factoidal webdav-user FILE NAME [--iterations N]

Reads the password from standard input (on a terminal it asks, and does not
show what you type; else it reads all of standard input, without one final
line end). Makes a 16-byte salt from the host's random source, derives
PBKDF2-HMAC-SHA256 with WebCrypto, and writes the line
NAME:pbkdf2-sha256:ITERATIONS:SALT_B64:HASH_B64 in FILE: in place of NAME's
line, or at the end. FILE is made when it does not exist, and is always
written with mode 0600 (a new file renamed over the old one).

  --iterations N   the PBKDF2 iteration count (default 600000, the OWASP
                   Password Storage Cheat Sheet figure of 2023 for
                   PBKDF2-HMAC-SHA256; at least 100000)

Every decision (the name rules, the password rules, the count, the line) is
in formal/lean4/L4Factoidal/WebDAV/Login.lean. Expert review:
https://github.com/danbri/factoidal/issues/1117 (https://github.com/danbri/factoidal/issues/1108).`,

  'solid-client': `factoidal solid-client - run one Solid client operation

usage: factoidal solid-client <get|put|post|delete|discover> URL [options]

Every request is built by the engine's solidClientRequest operation and
every response is read by solidClientResponse. This command supplies a
socket and prints what the engine answered.

The five verbs are aliases for the operation kinds of the wasm ABI; the
kind names are accepted directly as well.

  get       read              put     replace          post   create
  delete    delete            discover discoverStorage
  (also: patch, readProfile)

  --body TEXT       the request body for put, post and patch
  --file PATH       read the request body from a file
  --content-type M  the body's media type
  --interpret KIND  one of storage, containment, auxiliaries, profile,
                    wacAllow, used when the engine names none

Specification: https://solidproject.org/TR/protocol`,

  'lws-client': `factoidal lws-client - run one Linked Web Storage client operation

usage: factoidal lws-client <op> URL [options]

Every request is chosen and built by the engine (lwsClientStart,
lwsClientStep; formal/lean4/L4Factoidal/LWS/Client/): the authorization
flow with its discovery checks, preconditions, retries, paging and linksets.
This command supplies a socket and prints the engine's result as JSON. It
exits 1 when the operation fails, and prints the failure document.

operations:
  discover URL        read the storage description of the storage of URL
  read URL | head URL | getAccess URL
  create CONTAINER    --body/--file, --content-type, --slug, --container,
                      --type IRI, --link VALUE
  update URL          --body/--file, --content-type, --link VALUE
  patch URL           --body/--file (JSON Patch unless --content-type)
  delete URL          --recursive
  readLinkset URL | updateLinkset URL (--body/--file, --content-type)
  move URL            --destination CONTAINER
  list CONTAINER      every page, following rel="next"
  typeIndex URL | search URL --query JSON
  subscribe URL       --inbox URL [--topic URL]
  --endpoint URL      typeIndex, search, subscribe: the service endpoint;
                      the storage description is not read (for subscribe,
                      URL is the default topic)
  unsubscribe URL | revokeAccess URL
  requestAccess URL | grantAccess URL
                      --action A[,A] --assignee URI [--target URL[,URL]]
                      [--inbox URL]; or --policies JSON, an array of
                      {actions, assignee, targets, constraint?}, one
                      member per policy of the document

preconditions (update, patch, delete, updateLinkset, move):
  --if-match TAG | --if-match-current | --if-none-match-star |
  --if-unmodified-since DATE | --no-precondition
  --if-none-match TAG[,TAG]   If-None-Match with entity tags (RFC 9110
                      §13.1.2), alone or with --if-match TAG,
                      --if-match-current or --if-unmodified-since;
                      for read, the condition of the GET (304 is
                      notModified)
  (default: --if-match-current for update, patch, updateLinkset and move)
  --retry-412 N       read the tag again and resend, at most N times

authorization:
  --subject-token-file FILE   the credential to exchange (RFC 8693)
  --subject-token-type URI    its type, for example
                              urn:ietf:params:oauth:token-type:saml2
  --access-token TOKEN        a token to present to the storage of URL
                              (with --storage IRI and --root URL)
  --legacy-challenge          follow a 401 with only the challenge
                              Bearer as_uri="AS", realm="STORAGE" of the
                              drafts before 2026-10-19 (off by default: it
                              skips two discovery checks of lws10-core)
  --require-https             send no request to a URL that is not https
                              (the operation, discovery, metadata, the
                              authorization server, the token endpoint);
                              such an operation fails with insecureTransport

Draft: https://w3c.github.io/lws-protocol/lws10-core/`
}

// ------------------------------------------------------------- arguments

/**
 * Split argv into positional arguments and options. `--name value` and
 * `--name=value` both work; a flag with no value is `true`.
 */
function parseArguments (args, valueOptions) {
  const positional = []
  const options = Object.create(null)
  for (let index = 0; index < args.length; index += 1) {
    const argument = args[index]
    if (argument === '--') {
      positional.push(...args.slice(index + 1))
      break
    }
    if (argument === '-h') {
      options.help = true
      continue
    }
    if (!argument.startsWith('--')) {
      positional.push(argument)
      continue
    }
    const equals = argument.indexOf('=')
    const name = equals < 0 ? argument.slice(2) : argument.slice(2, equals)
    // An option named in REPEATABLE_OPTIONS keeps every value, in order.
    const keep = (value) => {
      if (REPEATABLE_OPTIONS.has(name)) {
        options[name] = Array.isArray(options[name]) ? [...options[name], value] : [value]
      } else {
        options[name] = value
      }
    }
    if (equals >= 0) {
      keep(argument.slice(equals + 1))
      continue
    }
    if (valueOptions.has(name)) {
      index += 1
      if (index >= args.length) {
        throw new UsageError(`option --${name} needs a value`)
      }
      keep(args[index])
      continue
    }
    options[name] = true
  }
  return { positional, options }
}

class UsageError extends Error {}

/** Options that may be given more than once; their value is the list. */
const REPEATABLE_OPTIONS = new Set(['cors-origin', 'saml-idp', 'saml-decrypt-key', 'allow-host', 'allow-origin'])

const VALUE_OPTIONS = {
  version: new Set([]),
  'sample-store': new Set([]),
  inspect: new Set(['generation']),
  query: new Set(['query', 'file', 'format', 'limit', 'base', 'generation']),
  pack: new Set(['layout', 'syntax', 'chunk-bytes', 'base', 'batch-bytes']),
  activate: new Set([]),
  update: new Set(['update', 'file']),
  compact: new Set([]),
  serve: new Set(['port', 'host', 'query-path', 'gsp-path', 'file', 'layout', 'tdb2', 'allow-host', 'allow-origin']),
  'lws-serve': new Set(['port', 'host', 'base', 'issuer', 'auth-config', 'owner', 'root-acl',
    'audience', 'page-size', 'moves', 'controller-inbox', 'delivery-limit', 'delivery-window',
    'redirects-max', 'storage', 'cors-origin', 'authz', 'alg', 'token-lifetime', 'rotate-after',
    'saml-idp', 'saml-decrypt-key', 'allow-host', 'allow-origin']),
  'solid-serve': new Set(['port', 'host', 'base', 'owner', 'issuer', 'auth-config', 'allow-host', 'allow-origin']),
  'solid-client': new Set(['body', 'file', 'content-type', 'interpret']),
  'lws-client': new Set(['body', 'file', 'content-type', 'slug', 'type', 'link', 'if-match',
    'if-unmodified-since', 'retry-412', 'destination', 'query', 'topic', 'action', 'assignee',
    'target', 'subject-token-file', 'subject-token-type', 'access-token', 'storage', 'root',
    'inbox', 'endpoint', 'if-none-match', 'policies']),
  'authz-serve': new Set(['port', 'host', 'issuer', 'resource', 'alg', 'token-lifetime', 'rotate-after',
    'cors-origin', 'saml-idp', 'saml-decrypt-key']),
  'authz-keys': new Set([]),
  'xmpp-serve': new Set(['port', 'host', 'domain', 'accounts', 'cert', 'key']),
  'webdav-serve': new Set(['port', 'host', 'users', 'cert', 'key', 'login-limit', 'login-window', 'xmpp', 'xmpp-password-file',
    'xmpp-host', 'xmpp-port', 'xmpp-allow', 'xmpp-resource', 'xmpp-ca', 'allow-host', 'allow-origin']),
  'webdav-user': new Set(['iterations']),
  'xmpp-http-proxy': new Set(['port', 'host', 'xmpp', 'xmpp-password-file', 'target', 'xmpp-host', 'xmpp-port',
    'xmpp-resource', 'xmpp-ca', 'timeout']),
  'lws-keygen': new Set([])
}

// ------------------------------------------------------------- commands

function packageDirectory () {
  return fileUrlToPath(new URL('..', import.meta.url).href)
}

function readJsonFile (path) {
  const bytes = readWhole(path)
  return JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes))
}

async function sha256Hex (bytes) {
  const digest = await globalThis.crypto.subtle.digest('SHA-256', bytes)
  return hexOfBytes(new Uint8Array(digest))
}

// `factoidal version`: what l4-assets/version.json says (the release stamp,
// written by tools/fetch-builds.sh --set web from the factoidal-builds
// release that built the wasm), what the installed wasm files hash to, and
// the loaded engine's own version(). A stamp whose sha256 differs from the
// installed wasm is an error (exit 1): the stamp then describes another
// build. A source checkout carries the unstamped placeholder.
async function commandVersion (options) {
  const root = packageDirectory()
  const own = readJsonFile(joinPath(root, 'package.json'))
  let stamp = null
  try {
    stamp = readJsonFile(joinPath(root, 'l4-assets/version.json'))
  } catch (_error) {
    stamp = null
  }
  const stamped = stamp !== null && stamp.stamped === true
  const installed = {}
  for (const [key, file] of [['wasm', 'l4factoidal.wasm']]) {
    try {
      const bytes = readWhole(joinPath(root, `l4-assets/${file}`))
      installed[key] = { sha256: await sha256Hex(bytes), bytes: bytes.length }
    } catch (_error) {
      installed[key] = null
    }
  }
  let engineVersion = null
  let engineError = null
  if (installed.wasm !== null) {
    try {
      engineVersion = (await loadEngine()).version()
    } catch (error) {
      engineError = String(error && error.message ? error.message : error)
    }
  }
  const mismatches = []
  if (stamped) {
    for (const [key, shaKey, bytesKey] of [['wasm', 'wasmSha256', 'wasmBytes']]) {
      if (installed[key] === null) continue
      if (stamp[shaKey] !== installed[key].sha256 || stamp[bytesKey] !== installed[key].bytes) {
        mismatches.push(`${key}: version.json says sha256 ${stamp[shaKey]} (${stamp[bytesKey]} bytes), ` +
          `installed file is ${installed[key].sha256} (${installed[key].bytes} bytes)`)
      }
    }
    if (engineVersion !== null && typeof stamp.engineVersion === 'string' &&
        stamp.engineVersion !== engineVersion) {
      mismatches.push(`engine: version.json says ${stamp.engineVersion}, the loaded wasm says ${engineVersion}`)
    }
  }
  const report = {
    package: own.name,
    version: own.version,
    host: runtime,
    stamp: stamp === null
      ? null
      : stamped
        ? {
            stamped: true,
            engineVersion: stamp.engineVersion,
            gitSha: stamp.gitSha,
            builtAt: stamp.builtAt,
            release: stamp.release,
            leanToolchain: stamp.leanToolchain,
            wasmSha256: stamp.wasmSha256,
            wasmBytes: stamp.wasmBytes
          }
        : { stamped: false, status: stamp.status || 'stamped at release' },
    installed,
    engineVersion,
    engineError,
    mismatches
  }
  if (options.json) {
    out(JSON.stringify(report, null, 2))
  } else {
    out(`${report.package} ${report.version}`)
    out(`host-io ${report.host}`)
    if (stamp === null) {
      out('stamp: no l4-assets/version.json in this install')
    } else if (!stamped) {
      out('stamp: not stamped (l4-assets/version.json is the source placeholder; ' +
        'it is stamped at release by tools/fetch-builds.sh --set web)')
    } else {
      out(`stamp: built from ${stamp.gitSha} at ${stamp.builtAt}` +
        (stamp.release ? ` (${stamp.release})` : ''))
      out(`stamp: engine ${stamp.engineVersion} (${stamp.leanToolchain})`)
      out(`stamp: wasm sha256 ${stamp.wasmSha256} (${stamp.wasmBytes} bytes)`)
    }
    for (const [key, label] of [['wasm', 'wasm']]) {
      out(installed[key] === null
        ? `installed ${label}: absent`
        : `installed ${label} sha256 ${installed[key].sha256} (${installed[key].bytes} bytes)`)
    }
    out(engineVersion !== null
      ? `engine version() ${engineVersion}`
      : `engine version() unavailable${engineError ? ': ' + engineError : ''}`)
  }
  if (mismatches.length > 0) {
    for (const m of mismatches) err(`factoidal version: STAMP MISMATCH ${m}`)
    return EXIT_FAILURE
  }
  return EXIT_OK
}


// ------------------------------------------------------------ rendering

/**
 * One graph name as the manifest reports it. `{"kind":"default"}` is the
 * default graph; the operation marks it that way so a host never has to
 * recognise a reserved IRI. The engine writes the N-Triples form of a name
 * (op termsToNTriples).
 */
function graphLabels (engine, graphs) {
  const terms = graphs.filter((g) => g.kind !== 'default')
    .map((g) => ({ type: g.kind === 'iri' ? 'uri' : 'bnode', value: g.value }))
  const tokens = terms.length === 0 ? [] : engine.call('termsToNTriples', [JSON.stringify(terms)]).tokens
  let k = 0
  return graphs.map((g) => (g.kind === 'default' ? 'default' : tokens[k++]))
}

/**
 * The SPARQL Query Results JSON terms of a table, as display cells: the
 * engine writes each term's canonical N-Triples form (op termsToNTriples).
 * `--format json` prints the engine's own document.
 */
function cellsOfRows (engine, rows) {
  const terms = []
  for (const row of rows) for (const t of row) if (t !== undefined && t !== null) terms.push(t)
  const tokens = terms.length === 0 ? [] : engine.call('termsToNTriples', [JSON.stringify(terms)]).tokens
  let k = 0
  return rows.map((row) => row.map((t) => (t === undefined || t === null ? '' : tokens[k++])))
}

function plural (count, noun) {
  return `${count} ${noun}${count === 1 ? '' : 's'}`
}

/** Print rows as columns padded to their widest cell. */
function printTable (headers, rows) {
  const widths = headers.map((header) => header.length)
  for (const row of rows) {
    for (let index = 0; index < row.length; index += 1) {
      if (row[index].length > widths[index]) widths[index] = row[index].length
    }
  }
  const line = (cells) => cells
    .map((cell, index) => index === cells.length - 1 ? cell : cell.padEnd(widths[index]))
    .join('  ')
  out(line(headers))
  for (const row of rows) out(line(row))
}

// --------------------------------------------------------------- SBM11

let sbm11 = null

/** The SBM11 functions of lib/sbm11.mjs over this command's engine, with
 *  the Node directory reader as the default reader (it moves bytes only). */
function sbm11Functions () {
  if (sbm11 === null) {
    setDefaultSbm11Reader(nodeDefaultReaderFactory())
    sbm11 = sbm11Api(loadEngine)
  }
  return sbm11
}

/**
 * The engine's answer (op storeLayout) when `source` holds an SBM11
 * generation, or names one through CURRENT: `{layout, generation,
 * manifest}`. null for an IBK store, for a directory the op does not
 * recognise, and for an engine built before the op; the IBK path then
 * runs, and reports a missing store in its own words.
 */
function sbm11Layout (engine, source) {
  sbm11Functions()
  let answer
  try {
    answer = engine.call('storeLayout', [source])
  } catch (_error) {
    return null
  }
  return answer && answer.layout === 'sbm11' ? answer : null
}

/** The directory a command reads: STORE, or STORE/GENERATION when
 *  --generation names one. */
function storeSource (root, named) {
  return named === null ? root : joinPath(root, named)
}

/** The engine's words of a refusal, without the loader's prefix. */
function engineWords (error) {
  const message = error && error.message ? String(error.message) : String(error)
  return message.replace(/^l4factoidal:\s*/, '')
}

async function inspectSbm11 (root, named, layout, options) {
  let store
  try {
    store = await sbm11Functions().openSbm11(storeSource(root, named))
  } catch (error) {
    err(`factoidal inspect: ${engineWords(error)}`)
    return EXIT_FAILURE
  }
  const terms = store.terms
  store.close()
  const generation = named !== null ? named : layout.generation
  const generationDir = named !== null || layout.generation === ''
    ? storeSource(root, named)
    : joinPath(root, layout.generation)
  const files = listGeneration(generationDir)
  let directoryBytes = 0
  for (const file of files) directoryBytes += file.size
  if (options.json) {
    out(JSON.stringify({
      ok: true,
      layout: 'sbm11',
      generation,
      activated: named === null && layout.generation !== '',
      manifest: layout.manifest,
      terms,
      files: files.length,
      bytes: directoryBytes
    }, null, 2))
    return EXIT_OK
  }
  out(`store ${root}`)
  if (named !== null) out(`generation ${generation} (named on the command line)`)
  else if (layout.generation !== '') out(`generation ${generation} (activated through CURRENT)`)
  else out('generation directory (no CURRENT)')
  out(`manifest ${layout.manifest}`)
  out('layout sbm11')
  out(plural(terms, 'term'))
  out(`generation directory holds ${files.length} files, ${directoryBytes} bytes`)
  return EXIT_OK
}

/**
 * Answer a query on an SBM11 store (ops sbm11Open / sbm11Query /
 * sbm11Close) and print it as `query` prints an IBK answer. The engine
 * answers SPARQL Query Results JSON for SELECT and ASK and N-Triples for
 * CONSTRUCT and DESCRIBE; this only chooses which renderer prints it.
 */
async function querySbm11 (engine, root, named, sparql, format, limit, options) {
  const quiet = options.quiet === true
  if (options.explain === true) {
    err('factoidal query: --explain prints the plan of an IBK store; there is ' +
      'no plan operation for an SBM11 store yet ' +
      '(https://github.com/danbri/factoidal/issues/1009)')
    return EXIT_FAILURE
  }
  let answer
  try {
    const store = await sbm11Functions().openSbm11(storeSource(root, named))
    try {
      const got = store.query(sparql)
      // read the bytes while the handle is open
      answer = { path: got.path, format: got.format, reads: got.reads,
        bytesRead: got.bytesRead, text: got.result }
    } finally {
      store.close()
    }
  } catch (error) {
    err(`factoidal query: ${engineWords(error)}`)
    if (isStackOverflow(error)) {
      for (const line of stackLimitAdvice(STACK_REMEDY.query)) err(line)
    }
    return EXIT_FAILURE
  }
  if (!quiet) {
    err(`${answer.path}, ${plural(answer.reads, 'read')}, ${answer.bytesRead} bytes read`)
  }
  let result
  if (answer.format === 'srj') {
    const document = JSON.parse(answer.text)
    if (typeof document.boolean === 'boolean') {
      if (format === 'json') {
        out(JSON.stringify(document, null, 2))
        return EXIT_OK
      }
      result = { kind: 'ask', boolean: document.boolean }
    } else {
      result = { kind: 'select', srj: document }
    }
  } else {
    result = { kind: 'construct', nquads: answer.text }
  }
  return renderQueryResult(engine, result, format, limit, quiet)
}

// ------------------------------------------------------------- inspect

async function commandInspect (positional, options) {
  if (positional.length !== 1) throw new UsageError('inspect needs exactly one STORE')
  const root = positional[0]
  const named = typeof options.generation === 'string' ? options.generation : null
  const engine = await loadEngine()
  const layout = sbm11Layout(engine, storeSource(root, named))
  if (layout !== null) return inspectSbm11(root, named, layout, options)
  const store = openStore(root, named)
  const envelope = inspectManifest(engine, store)

  if (options.json) {
    // The operation's envelope, unchanged.
    out(JSON.stringify(envelope, null, 2))
    return EXIT_OK
  }

  const files = listGeneration(store.generationDir)
  let directoryBytes = 0
  for (const file of files) directoryBytes += file.size

  out(`store ${root}`)
  out(`generation ${store.generation}${store.activated ? ' (activated through CURRENT)' : ' (named on the command line)'}`)
  out(`manifest ${store.manifestName}, ${store.manifest.length} bytes, wire version ${envelope.wireVersion}`)
  out(`layout ${envelope.layout}`)
  out(`blank-node profile ${envelope.blankNodeProfile === '' ? '(none recorded)' : envelope.blankNodeProfile}`)
  out(`term registry ${envelope.termRegistryVersion === '' ? '(none recorded)' : envelope.termRegistryVersion}`)
  out(`fixed-chunk Merkle commitment ${envelope.rangeCommitted ? 'yes' : 'no'}`)
  out(`${envelope.entries.length} ${envelope.entries.length === 1 ? 'entry' : 'entries'}, ${envelope.totalBytes} bytes, ${plural(envelope.totalRows, 'row')}`)
  // Wire version 10: the manifest blob table. Each `blob-<hex>.lit` holds the
  // lexical form of one literal above the 65,536-byte inline ceiling, and is
  // shared by every block whose dictionary names it.
  const blobs = envelope.blobs ?? []
  if (blobs.length > 0) {
    let blobBytes = 0
    for (const blob of blobs) blobBytes += blob.bytes
    out(`${plural(blobs.length, 'out-of-line literal')}, ${blobBytes} bytes`)
  }
  out(`generation directory holds ${files.length} files, ${directoryBytes} bytes`)
  out('')
  // The zone maps are per entry, so the columns appear only for a manifest
  // that carries them. A bound is the first 64 bytes of the smallest (or
  // largest) term key of the block; the first eight are enough to see that
  // two blocks hold different ranges.
  const zoned = envelope.entries.some((entry) => entry.subjectZone !== undefined)
  const zoneCell = (zone) =>
    zone === undefined ? '-' : `${zone.min.slice(0, 16)}..${zone.max.slice(0, 16)}`
  printTable(
    ['#', 'rows', 'bytes', 'kind', 'graphs', 'predicate']
      .concat(zoned ? ['blobs', 'subject zone'] : []),
    envelope.entries.map((entry) => [
      String(entry.ordinal),
      String(entry.rows),
      String(entry.bytes),
      entry.blockKind,
      entry.graphs.length === 0 ? '-' : graphLabels(engine, entry.graphs).join(' '),
      entry.predicate
    ].concat(zoned
      ? [String((entry.blobRefs ?? []).length), zoneCell(entry.subjectZone)]
      : [])))
  return EXIT_OK
}

function notWired (command, detail) {
  err(`factoidal ${command}: not yet wired. ${detail}`)
  err(`This needs a WebAssembly operation from the Lean engine; see ${ISSUE}.`)
  return EXIT_NOT_WIRED
}

const QUERY_FORMATS = ['table', 'json', 'nquads', 'turtle']
const UNAVAILABLE_FORMATS = {
  xml: 'the SPARQL Results XML document',
  csv: 'the SPARQL Results CSV document',
  tsv: 'the SPARQL Results TSV document'
}

function queryText (positional, options) {
  if (typeof options.file === 'string') {
    return new TextDecoder('utf-8', { fatal: true }).decode(readWhole(options.file))
  }
  if (positional.length > 1) return positional.slice(1).join(' ')
  if (typeof options.query === 'string') return options.query
  throw new UsageError('query needs QUERY, --query TEXT or --file PATH')
}

function queryFormat (options) {
  if (options.json === true && typeof options.format !== 'string') return 'json'
  if (typeof options.format !== 'string') return 'table'
  const format = options.format.toLowerCase()
  if (QUERY_FORMATS.indexOf(format) >= 0) return format
  if (Object.prototype.hasOwnProperty.call(UNAVAILABLE_FORMATS, format)) {
    throw new UsageError(
      `--format ${format} needs an engine operation that writes ` +
      `${UNAVAILABLE_FORMATS[format]}; there is none, and writing one here ` +
      'would be a second serializer. Use --format json.')
  }
  throw new UsageError(`--format ${options.format} is not one of ${QUERY_FORMATS.join(', ')}`)
}

function queryLimit (options, format) {
  if (typeof options.limit !== 'string') return null
  const limit = Number(options.limit)
  if (!Number.isSafeInteger(limit) || limit < 0) {
    throw new UsageError('--limit needs a non-negative whole number')
  }
  if (format !== 'table') {
    throw new UsageError(
      '--limit truncates the printed table only; it is not carried into the ' +
      "engine's own documents. Put a LIMIT clause in the query instead.")
  }
  return limit
}

/** Report a refusal the store operations made, and what to do about it. */
function reportStoreFailure (error) {
  err(`factoidal query: ${error.message}`)
  if (error.capLimit !== null) {
    err(`This query needs more of the store than one WebAssembly call may read: ${error.capValue} against a cap of ${error.capLimit}.`)
    err('Narrow the query - bind a predicate, or restrict the graph - or use the native l4block-* tools.')
  } else if (error.stackLimit) {
    for (const line of stackLimitAdvice(STACK_REMEDY.query)) err(line)
  } else if (error.digestKey !== null) {
    err(`The bytes of '${error.digestKey}' in the generation directory are not the bytes the manifest commits.`)
    err('The generation is damaged or was edited after it was packed; repack or restore it.')
  }
  return EXIT_FAILURE
}

/**
 * Run one store call again on a bigger call stack, after the in-process
 * attempt ran out of frames.
 *
 * A one-shot query builds no handle and drops what it loads, so it runs
 * IN PROCESS first and pays nothing for a worker it would throw away.
 * This is the retry, and it is reached only by the overflow.
 *
 * Node takes the worker route; Deno has no `worker_threads` route with a
 * stack size, so it re-executes this command once with a raised V8 stack
 * (`denoReexec`), which needs --allow-run and --allow-env.
 *
 * @returns the retried answer, or a number to exit with (the Deno child's
 *   code), or null when no bigger stack is available here
 */
async function onBiggerStack (options, quiet, retry) {
  const host = { worker: options['no-worker'] !== true }
  if (host.worker === false) return null
  if (isDeno) {
    const code = await denoReexec(host)
    return typeof code === 'number' ? code : null
  }
  if (!workerRouteAvailable()) return null
  if (!quiet) {
    err('The runtime ran out of call stack; running again on a worker thread ' +
      'with a bigger one.')
  }
  return await retry()
}

async function commandQuery (positional, options) {
  if (positional.length < 1) throw new UsageError('query needs a STORE')
  if (typeof options.base === 'string') {
    throw new UsageError(
      'the store query operation takes no base argument; put a BASE clause ' +
      'in the query text instead')
  }
  const root = positional[0]
  const sparql = queryText(positional, options)
  const format = queryFormat(options)
  const limit = queryLimit(options, format)
  const quiet = options.quiet === true

  const named = typeof options.generation === 'string' ? options.generation : null
  const engine = await loadEngine()
  if (sbm11Layout(engine, storeSource(root, named)) !== null) {
    return querySbm11(engine, root, named, sparql, format, limit, options)
  }
  const store = openStore(root, named)

  if (options.explain === true) {
    let plan
    try {
      plan = planQuery(engine, store, sparql)
    } catch (error) {
      if (!(error instanceof StoreOperationError)) throw error
      if (!error.stackLimit) return reportStoreFailure(error)
      const retried = await onBiggerStack(options, quiet,
        () => planQueryOnWorker(root, named, sparql))
      if (retried === null) return reportStoreFailure(error)
      if (typeof retried === 'number') return retried
      plan = retried
    }
    if (format === 'json' || options.json === true) {
      out(JSON.stringify(plan, null, 2))
      return EXIT_OK
    }
    out(`layout ${plan.layout} (wire version ${plan.wireVersion})`)
    out(`mode ${plan.mode}`)
    out(`${plural(plan.shards, 'artifact')}, ${plan.bytes} bytes, ${plural(plan.rows, 'row')}`)
    for (const key of plan.keys) out(`  ${key}`)
    return EXIT_OK
  }

  let answer
  try {
    answer = queryStore(engine, store, sparql)
  } catch (error) {
    if (!(error instanceof StoreOperationError)) throw error
    if (!error.stackLimit) return reportStoreFailure(error)
    const retried = await onBiggerStack(options, quiet,
      () => queryStoreOnWorker(root, named, sparql))
    if (retried === null) return reportStoreFailure(error)
    if (typeof retried === 'number') return retried
    answer = retried
  }
  const { plan, result, blobBytes } = answer
  if (!quiet) {
    err(`mode ${result.mode}, ${plural(result.shards, 'artifact')}, ${blobBytes} bytes read, plan declares ${plural(plan.rows, 'block row')}`)
  }
  return renderQueryResult(engine, result, format, limit, quiet)
}

function renderQueryResult (engine, result, format, limit, quiet) {
  if (result.kind === 'select') {
    const vars = result.srj.head.vars
    const bindings = result.srj.results.bindings
    if (format === 'json') {
      out(JSON.stringify(result.srj, null, 2))
      return EXIT_OK
    }
    if (format !== 'table') {
      err(`factoidal query: --format ${format} needs a CONSTRUCT or DESCRIBE query; this one is a SELECT`)
      return EXIT_FAILURE
    }
    const shown = limit === null ? bindings : bindings.slice(0, limit)
    printTable(vars, cellsOfRows(engine, shown.map((row) => vars.map((name) => row[name]))))
    if (shown.length < bindings.length) {
      err(`showing ${shown.length} of ${bindings.length} rows (--limit ${limit})`)
    } else if (!quiet) {
      err(plural(bindings.length, 'row'))
    }
    return EXIT_OK
  }
  if (result.kind === 'ask') {
    if (format === 'json') {
      // The operation answers ASK with a boolean, not with a results
      // document, so the envelope is what there is to print.
      out(JSON.stringify(result, null, 2))
      return EXIT_OK
    }
    if (format !== 'table') {
      err(`factoidal query: --format ${format} needs a CONSTRUCT or DESCRIBE query; this one is an ASK`)
      return EXIT_FAILURE
    }
    out(result.boolean ? 'true' : 'false')
    return EXIT_OK
  }
  if (result.kind === 'construct' || result.kind === 'describe') {
    if (format === 'json') {
      out(JSON.stringify(result, null, 2))
      return EXIT_OK
    }
    if (format === 'turtle') {
      out(turtleOfNQuads(engine, result.nquads))
      return EXIT_OK
    }
    // table and nquads both print what the engine serialized.
    if (result.nquads.length > 0) out(result.nquads.replace(/\n$/, ''))
    return EXIT_OK
  }
  err(`factoidal query: the engine answered an unknown result kind "${result.kind}"`)
  return EXIT_FAILURE
}

/** The first `length` bytes of a file, as text, for content detection. */
function readHead (path, length) {
  return new TextDecoder('utf-8', { fatal: false }).decode(readChunk(path, 0, length))
}

/** The syntax tag for an input: --syntax when given, else the engine's
 *  suffix table (op engineTables), else the engine's content detection
 *  (op detectFormat) on the first 64 KiB of the file. */
function packSyntax (engine, input, options, layout) {
  const tables = engine.call('engineTables', []).tables
  // The SBM11 pack reads the whole document (op sbm11PackFiles), so it also
  // reads the syntaxes of packWholeSuffixes (RDF/XML, JSON-LD).
  const whole = layout === 'sbm11' ? (tables.packWholeSuffixes ?? {}) : {}
  const syntaxes = tables.packSyntaxes.slice()
  for (const syntax of Object.values(whole)) {
    if (syntaxes.indexOf(syntax) < 0) syntaxes.push(syntax)
  }
  if (typeof options.syntax === 'string') {
    const syntax = options.syntax.toLowerCase()
    if (syntaxes.indexOf(syntax) >= 0) return syntax
    throw new UsageError(`--syntax ${options.syntax} is not one of ${syntaxes.join(', ')}`)
  }
  const lower = input.toLowerCase()
  for (const [suffix, syntax] of Object.entries(tables.packSuffixes)) {
    if (lower.endsWith(suffix)) return syntax
  }
  for (const [suffix, syntax] of Object.entries(whole)) {
    if (lower.endsWith(suffix)) return syntax
  }
  for (const [suffix, name] of Object.entries(tables.packUnsupportedSuffixes)) {
    if (lower.endsWith(suffix)) {
      throw new UsageError(
        `pack does not read ${name}. The packer reads ` +
        `${syntaxes.join(', ')} only${layout === 'sbm11' ? '' : ' (--layout sbm11 also reads rdfxml and jsonld)'}. Convert the file first, for ` +
        "example with: factoidal parse FILE --out nquads")
    }
  }
  let head = ''
  try {
    head = readHead(input, 65536)
  } catch (_error) {
    head = ''
  }
  if (head !== '') {
    const tag = engine.call('detectFormat', [head]).format
    const syntax = tag.replace(/12$/, '')
    if (syntaxes.indexOf(syntax) >= 0) return syntax
  }
  throw new UsageError(
    `cannot tell the syntax of ${input} from its name or its content; give --syntax ` +
    `(${syntaxes.join(', ')})`)
}


/**
 * The base IRI relative IRIs in the source resolve against.
 *
 * The native packer uses `file://<input>`, so this matches it by default
 * and byte-identical output needs no flag. `--base` overrides it, and
 * `--base ''` asks for no base, which turns a relative IRI into a parse
 * error rather than a silently different term.
 */
function packBase (input, options, layout) {
  if (typeof options.base === 'string') return options.base
  // `l4sbm11-pack` uses no base unless --base names one; the same default
  // gives the same bytes.
  if (layout === 'sbm11') return ''
  const absolute = input.startsWith('/') ? input : joinPath(currentDirectory(), input)
  return 'file://' + absolute
}

/** The process's working directory, on Node and on Deno. */
function currentDirectory () {
  if (isDeno) return globalThis.Deno.cwd()
  return process.cwd()
}

function packLayout (options) {
  if (typeof options.layout !== 'string') return 'ibk5'
  const layout = options.layout.toLowerCase()
  if (PACK_LAYOUTS.indexOf(layout) >= 0) return layout
  throw new UsageError(`--layout ${options.layout} is not one of ${PACK_LAYOUTS.join(', ')}`)
}

async function commandPack (positional, options) {
  if (positional.length !== 2) throw new UsageError('pack needs INPUT and OUTPUT')
  const [input, output] = positional
  const layout = packLayout(options)
  const syntax = packSyntax(await loadEngine(), input, options, layout)
  // The pack fold needs a bigger call stack than either runtime gives by
  // default (https://github.com/danbri/factoidal/issues/649). Under Node
  // the work runs on a worker thread with a raised stack; under Deno the
  // command re-executes itself once with --v8-flags=--stack-size, and
  // this is where that happens, before any file is opened. --no-worker
  // keeps the in-process path testable.
  const host = { worker: options['no-worker'] !== true }
  const reexec = await denoReexec(host)
  if (reexec !== null) return reexec
  makeDirectory(output)
  const quiet = options.quiet === true
  let answer
  try {
    answer = await runPack(
      layout === 'sbm11'
        ? { kind: 'packSbm11', input, output, syntax, base: packBase(input, options, layout) }
        : { kind: 'pack', input, output, syntax, layout, base: packBase(input, options, layout),
            batchBytes: options['batch-bytes'] },
      quiet
        ? undefined
        : (progress) => {
            if (progress.bytesRead % (16 * 1024 * 1024) < FEED_PROGRESS) {
              err(`${progress.pass}: ${progress.bytesRead} bytes read, ${progress.artifacts} artifacts written`)
            }
          },
      host)
  } catch (error) {
    if (error instanceof PackError || error instanceof StoreHostError) {
      err(`factoidal pack: ${error.message}`)
      return EXIT_FAILURE
    }
    // Everything the engine refuses -- an unknown grammar tag, a parse
    // error, a cap -- arrives as a plain Error carrying the engine's own
    // words. A stack trace here would hide them.
    if (error instanceof Error && typeof error.message === 'string') {
      err(`factoidal pack: ${error.message.replace(/^l4factoidal:\s*/, '')}`)
      // The raised stack was refused, unavailable, or still not enough.
      if (isStackOverflow(error)) {
        for (const line of stackLimitAdvice(STACK_REMEDY.pack)) err(line)
      }
      return EXIT_FAILURE
    }
    throw error
  }
  if (answer.notWired === true) {
    return notWired('pack',
      'This install carries an engine built before the streaming pack ' +
      'operations. Update @factoidal/core, or set FACTOIDAL_L4_ASSETS to ' +
      'a newer build.')
  }
  const report = answer.report
  if (options.json === true) {
    out(JSON.stringify(report, null, 2))
    return EXIT_OK
  }
  out(`packed ${report.bytesRead} bytes of ${syntax} into ${output}`)
  out(`${report.written.length} ${layout === 'sbm11' ? 'files' : 'artifacts'}, ${report.bytesWritten} bytes, layout ${layout}`)
  if (typeof report.rows === 'number') out(`${plural(report.rows, 'row')}`)
  out(`activate it with: factoidal activate ${dirOf(output)} ${nameOf(output)}`)
  return EXIT_OK
}

async function commandSampleStore (positional, options) {
  if (positional.length > 1) throw new UsageError('sample-store takes at most one DIR')
  // Re-execute here, once, before any work. The pack and the activate
  // below would each re-execute the whole command line under Deno, and
  // each child printed the path again (three lines, 2026-10-24).
  const reexec = await denoReexec({ worker: options['no-worker'] !== true })
  if (reexec !== null) return reexec
  const { mkdtempSync, writeFileSync, existsSync } = await import('node:fs')
  const { tmpdir } = await import('node:os')
  const root = positional.length === 1
    ? positional[0]
    : mkdtempSync(joinPath(tmpdir(), 'factoidal-sample-store-'))
  if (!existsSync(joinPath(root, 'CURRENT'))) {
    makeDirectory(joinPath(root, 'gen-1'))
    const source = joinPath(root, 'sample.ttl')
    writeFileSync(source, SAMPLE_TURTLE)
    outSilenced = true
    try {
      let code = await commandPack([source, joinPath(root, 'gen-1')], { quiet: true })
      if (code === EXIT_OK) code = await commandActivate([root, 'gen-1'], { quiet: true })
      if (code !== EXIT_OK) return code
    } finally {
      outSilenced = false
    }
  }
  if (options.json === true) {
    out(JSON.stringify({ path: root, ...sampleStoreFacts }, null, 2))
  } else {
    out(root)
  }
  return EXIT_OK
}

async function commandActivate (positional, options) {
  if (positional.length !== 2) throw new UsageError('activate needs STORE and GENERATION')
  const [root, generation] = positional
  // Verification decodes the same blocks the pack encoded, so it recurses
  // as deep and needs the same raised stack. Measured 2026-09-04: a
  // 112,742-row generation packed successfully and then failed to
  // activate with `Maximum call stack size exceeded`, leaving a store
  // that could be built and not opened
  // (https://github.com/danbri/factoidal/issues/649).
  const host = { worker: options['no-worker'] !== true }
  const reexec = await denoReexec(host)
  if (reexec !== null) return reexec
  const engine = await loadEngine()
  if (sbm11Layout(engine, joinPath(root, generation)) !== null) {
    return activateSbm11(engine, root, generation, options)
  }
  let answer
  try {
    answer = await runPack({ kind: 'activate', root, generation }, undefined, host)
  } catch (error) {
    if (error instanceof PackError || error instanceof StoreHostError) {
      err(`factoidal activate: ${error.code ? error.code + ': ' : ''}${error.message}`)
      return EXIT_FAILURE
    }
    if (error instanceof Error && typeof error.message === 'string') {
      err(`factoidal activate: ${error.message.replace(/^l4factoidal:\s*/, '')}`)
      if (isStackOverflow(error)) {
        for (const line of stackLimitAdvice(STACK_REMEDY.pack)) err(line)
      }
      return EXIT_FAILURE
    }
    throw error
  }
  if (answer.notWired === true) {
    return notWired('activate',
      'This install carries an engine built before the activation ' +
      'verification operation. Update @factoidal/core.')
  }
  const verdict = answer.report
  if (verdict.ok !== true) {
    err(`factoidal activate: ${verdict.error}`)
    err('The generation is NOT activated; CURRENT is unchanged.')
    return EXIT_FAILURE
  }
  // Only now does the pointer move, and it moves atomically.
  const pointer = new TextEncoder().encode(generation)
  const synced = atomicReplace(joinPath(root, 'CURRENT'), pointer)
  if (options.json === true) {
    out(JSON.stringify({ ...verdict, generation, directorySynced: synced }, null, 2))
    return EXIT_OK
  }
  out(`activated ${generation}: ${verdict.artifacts} artifacts verified, ${verdict.bytes} bytes`)
  if (!synced) {
    err('CURRENT was replaced, but the directory entry was not synced; a ' +
        'crash now could lose the pointer update.')
  }
  return EXIT_OK
}

/**
 * Activate an SBM11 generation: the engine checks every file against the
 * manifest (op sbm11Verify), and only after its "ok" does CURRENT move.
 */
function activateSbm11 (engine, root, generation, options) {
  let verdict
  try {
    verdict = engine.call('sbm11Verify', [joinPath(root, generation)])
  } catch (error) {
    err(`factoidal activate: ${engineWords(error)}`)
    err('The generation is NOT activated; CURRENT is unchanged.')
    return EXIT_FAILURE
  }
  const synced = atomicReplace(joinPath(root, 'CURRENT'), new TextEncoder().encode(generation))
  if (options.json === true) {
    out(JSON.stringify({ ...verdict, layout: 'sbm11', generation, directorySynced: synced }, null, 2))
    return EXIT_OK
  }
  out(`activated ${generation}: ${verdict.artifacts} artifacts verified (${verdict.files} files, ${verdict.bytes} bytes), layout sbm11`)
  if (!synced) {
    err('CURRENT was replaced, but the directory entry was not synced; a ' +
        'crash now could lose the pointer update.')
  }
  return EXIT_OK
}

function commandUpdate (positional, options) {
  if (positional.length < 1) throw new UsageError('update needs a STORE')
  const text = positional.length > 1
    ? positional.slice(1).join(' ')
    : (typeof options.update === 'string' ? options.update : null)
  if (text === null && typeof options.file !== 'string') {
    throw new UsageError('update needs UPDATE, --update TEXT or --file PATH')
  }
  return notWired('update', 'The delta-log operations are stage 4 of the milestone.')
}

function commandCompact (positional, _options) {
  if (positional.length !== 2) throw new UsageError('compact needs STORE and GENERATION')
  return notWired('compact', 'Compaction is stage 4 of the milestone.')
}

// ------------------------------------------------- the protocol servers
// These commands hand a socket to a host module and print where it is
// listening. They decide nothing about the protocol they serve; see
// npm/factoidal/lws/README.md and npm/factoidal/solid/*/README.md.
// https://github.com/danbri/factoidal/issues/659

function servePort (options, fallback) {
  if (options.port === undefined) return fallback
  const port = Number(options.port)
  if (!Number.isInteger(port) || port < 0 || port > 65535) {
    throw new UsageError(`--port must be an integer from 0 to 65535, not "${options.port}"`)
  }
  return port
}

// --page-size N: a CLI number, passed unchanged as the engine config member
// `pageSize`; what a page holds is decided in L4Factoidal/LWS/Pagination.lean.
function pageSizeOption (value) {
  return natOption('page-size', value)
}

function natOption (flag, value) {
  const n = Number(value)
  if (!Number.isInteger(n) || n < 0) {
    throw new UsageError(`--${flag} must be a non-negative integer, not "${value}"`)
  }
  return n
}

// --cors-origin ORIGIN (repeatable) and --no-cors, as the config member
// `cors`: a list of origins, or false. Passed unread; the engine checks each
// origin and decides every CORS field (L4Factoidal/HTTP/Cors.lean). With
// neither option the member is absent and the engine echoes the request
// Origin (Solid Protocol section 8.1).
function corsConfig (options) {
  const origins = options['cors-origin']
  if (options['no-cors'] === true && origins !== undefined) {
    throw new UsageError('--no-cors cannot be combined with --cors-origin')
  }
  if (options['no-cors'] === true) return { cors: false }
  if (Array.isArray(origins)) return { cors: origins }
  return {}
}

// --allow-host NAME and --allow-origin ORIGIN (repeatable), as the config
// members `allowHosts` and `allowOrigins` of the Host and Origin guard of a
// listener without authentication. Passed unread; the engine checks each
// value and decides (L4Factoidal/HTTP/LocalGuard.lean,
// https://github.com/danbri/factoidal/issues/1124).
function localGuardConfig (options) {
  const out = {}
  if (Array.isArray(options['allow-host'])) out.allowHosts = options['allow-host']
  if (Array.isArray(options['allow-origin'])) out.allowOrigins = options['allow-origin']
  return out
}

function hasLocalGuardOptions (options) {
  return options['allow-host'] !== undefined || options['allow-origin'] !== undefined
}

// --saml-idp FILE (repeatable): a SAML 2.0 identity provider whose signed
// assertions the authorization server accepts, as the config member
// `samlIdps`. FILE is JSON {"entityId": ID, "jwk": RSA public JWK}; passed
// unread, the engine checks it (Wasm/Ops/Authz.lean, issue 926).
// --saml-decrypt-key FILE (repeatable): one private JWK, as the config member
// `samlKeys`; passed unread, the engine checks it (samlKeysOf?, issue 1073).
function samlConfig (options) {
  const out = {}
  const files = options['saml-idp']
  if (Array.isArray(files)) out.samlIdps = files.map((f) => readJsonFile(f))
  const keys = options['saml-decrypt-key']
  if (Array.isArray(keys)) out.samlKeys = keys.map((f) => readJsonFile(f))
  return out
}

function serveHost (options) {
  if (options.host === undefined) return '127.0.0.1'
  if (typeof options.host !== 'string' || options.host.length === 0) {
    throw new UsageError('--host needs an address')
  }
  return options.host
}

/** Keep the process alive until the runtime is interrupted. */
function untilInterrupted (running, quiet) {
  return new Promise((resolve) => {
    const stop = async () => {
      if (!quiet) err('')
      await running.close()
      resolve(EXIT_OK)
    }
    if (isDeno) {
      globalThis.Deno.addSignalListener('SIGINT', stop)
    } else {
      process.on('SIGINT', stop)
      process.on('SIGTERM', stop)
    }
  })
}

async function commandServe (positional, options) {
  const quiet = options.quiet === true
  // The Apache Jena Fuseki form: `serve --file DATA /ds`. The file is
  // packed into a new collection in a temporary directory (ibk5 unless
  // --layout says otherwise, so every graph accepts writes), activated, and
  // served at /ds/sparql and /ds/data; /ds/query, /ds/update and /ds/get
  // are answered too (StoreEndpoint.datasetPrefix). Updates go to that
  // temporary collection and are lost when the process ends, as with
  // fuseki-server --file. docs/fuseki-replacement.md.
  if (typeof options.file === 'string') {
    if (positional.length !== 1 || !positional[0].startsWith('/')) {
      throw new UsageError('serve --file DATA needs one dataset name, such as /ds')
    }
    const dsName = positional[0].replace(/\/+$/, '')
    const { mkdtempSync } = await import('node:fs')
    const { tmpdir } = await import('node:os')
    const { join } = await import('node:path')
    const root = mkdtempSync(join(tmpdir(), 'factoidal-serve-'))
    const packOptions = { quiet: true, layout: packLayout(options) }
    if (packOptions.layout === 'sbm11') {
      throw new UsageError('serve --file packs a store that accepts updates; --layout sbm11 ' +
        'packs a store that serve does not read yet. Use ibk3, ibk4 or ibk5.')
    }
    let rc = await commandPack([options.file, join(root, 'gen-1')], packOptions)
    if (rc !== 0) return rc
    rc = await commandActivate([root, 'gen-1'], { quiet: true })
    if (rc !== 0) return rc
    if (!quiet) err(`serve: packed ${options.file} into ${root} (temporary; updates are lost on exit)`)
    positional = [root]
    options = { ...options, 'query-path': `${dsName}/sparql`, 'gsp-path': `${dsName}/data` }
  }
  // The Apache Jena Fuseki form: `serve --tdb2 DIR /ds`, a TDB2 database
  // read in place and read only (https://github.com/danbri/factoidal/issues/834).
  const tdb2 = typeof options.tdb2 === 'string'
  if (tdb2) {
    if (positional.length !== 1 || !positional[0].startsWith('/')) {
      throw new UsageError('serve --tdb2 DIR needs one dataset name, such as /ds')
    }
    const dsName = positional[0].replace(/\/+$/, '')
    positional = [options.tdb2]
    options = { ...options, 'query-path': `${dsName}/sparql`, 'gsp-path': `${dsName}/data` }
  }
  if (positional.length !== 1) throw new UsageError('serve needs one STORE')
  if (!tdb2 && sbm11Layout(await loadEngine(), positional[0]) !== null) {
    err(`factoidal serve: ${positional[0]} is an SBM11 store, and serve reads IBK ` +
      'stores only (the storeServe operations). Query it with: factoidal query ' +
      `${positional[0]} QUERY (https://github.com/danbri/factoidal/issues/1009)`)
    return EXIT_FAILURE
  }
  const { listen, listenOnWorker, ServeHostError } = await import('./serve.mjs')
  const serveOptions = {
    port: servePort(options, 3030),
    host: serveHost(options),
    ...(tdb2 ? { tdb2: true } : {}),
    ...(typeof options['query-path'] === 'string' ? { queryPath: options['query-path'] } : {}),
    ...(typeof options['gsp-path'] === 'string' ? { gspPath: options['gsp-path'] } : {}),
    ...localGuardConfig(options)
  }
  const onWorker = options['no-worker'] !== true && workerRouteAvailable()
  let running
  try {
    running = onWorker
      ? await listenOnWorker(positional[0], serveOptions)
      : await listen(positional[0], serveOptions)
  } catch (error) {
    if (error instanceof ServeHostError && error.unknownOp) {
      return notWired('serve', error.message)
    }
    if (error instanceof Error && typeof error.message === 'string') {
      err(`factoidal serve: ${error.message.replace(/^l4factoidal:\s*/, '')}`)
      return EXIT_FAILURE
    }
    throw error
  }
  const info = onWorker ? running.info : running.served.info
  if (!quiet) {
    err(`serve: listening on ${running.origin} for ${positional[0]} ` +
      `(layout ${info.layout}, ${plural(info.rows, 'row')}, ` +
      `delta batches replayed: ${info.deltaBatches}, write scope ${info.writeScope})`)
    err(`serve: query ${running.origin}${info.queryPath}, graph store ${running.origin}${info.gspPath}`)
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

async function commandLwsServe (positional, options) {
  if (positional.length !== 1) throw new UsageError('lws-serve needs one DIR')
  const quiet = options.quiet === true
  const insecure = options['insecure-no-auth'] === true
  const issuerOption = typeof options.issuer === 'string' ? options.issuer : null
  const authFile = typeof options['auth-config'] === 'string' ? options['auth-config'] : null
  const authzDir = typeof options.authz === 'string' ? options.authz : null
  if (!insecure && issuerOption === null && authFile === null && authzDir === null) {
    throw new UsageError('lws-serve needs --authz DIR, --issuer IRI or --auth-config FILE, ' +
      'or --insecure-no-auth for development')
  }
  if (insecure && (issuerOption !== null || authFile !== null || authzDir !== null)) {
    throw new UsageError('--insecure-no-auth cannot be combined with --authz, --issuer or --auth-config')
  }
  if (!insecure && hasLocalGuardOptions(options)) {
    throw new UsageError('--allow-host and --allow-origin go with --insecure-no-auth; under authorization the token decides')
  }
  // --authz DIR: an authorization server on the same port, its issuer the
  // storage root (L4Factoidal/Authz/Mount.lean). Its options are passed
  // unread; the engine checks them (Wasm/Ops/Authz.lean).
  const authz = authzDir === null ? undefined : {
    dir: authzDir,
    ...(typeof options.alg === 'string' ? { alg: options.alg } : {}),
    ...(options['token-lifetime'] !== undefined ? { tokenLifetime: natOption('token-lifetime', options['token-lifetime']) } : {}),
    ...(options['rotate-after'] !== undefined ? { rotateAfter: natOption('rotate-after', options['rotate-after']) } : {}),
    ...(options['allow-http'] === true ? { allowHttp: true } : {}),
    ...(options['allow-private-fetch'] === true ? { allowPrivateFetch: true } : {}),
    ...corsConfig(options),
    ...samlConfig(options)
  }
  let auth
  if (authFile !== null) {
    auth = readJsonFile(authFile)
  } else if (issuerOption !== null) {
    auth = { issuers: issuerOption.split(',').filter((v) => v !== '').map((issuer) => ({ issuer })) }
  }
  if (auth !== undefined && typeof options.audience === 'string') {
    auth = { ...auth, audience: options.audience }
  }
  const { listen, LwsHostError } = await import('../lws/server.mjs')
  let running
  try {
    running = await listen({
      port: servePort(options, 3000),
      host: serveHost(options),
      ...(typeof options.base === 'string' ? { baseIri: options.base } : {}),
      ...(options['page-size'] !== undefined ? { pageSize: pageSizeOption(options['page-size']) } : {}),
      ...(options['unstable-search-results'] === true ? { searchResults: true } : {}),
      ...(options.merkle === true ? { merkle: true } : {}),
      // Passed unread as config members; the engine decides what they mean
      // and refuses a value it does not know (Wasm/Ops/Lws.lean).
      ...(options['paginate-always'] === true ? { paginateAlways: true } : {}),
      ...(typeof options.moves === 'string' ? { moves: options.moves } : {}),
      ...(options['no-linkset-put'] === true ? { linksetPut: false } : {}),
      ...(typeof options['controller-inbox'] === 'string' ? { controllerInbox: options['controller-inbox'] } : {}),
      ...(options['delivery-limit'] !== undefined ? { deliveryLimit: natOption('delivery-limit', options['delivery-limit']) } : {}),
      ...(options['delivery-window'] !== undefined ? { deliveryWindow: natOption('delivery-window', options['delivery-window']) } : {}),
      ...(options['redirects-max'] !== undefined ? { redirectsMax: natOption('redirects-max', options['redirects-max']) } : {}),
      ...(typeof options.storage === 'string' ? { storage: options.storage } : {}),
      ...corsConfig(options),
      ...(insecure ? { insecureNoAuth: true, ...localGuardConfig(options) } : { auth }),
      ...(authz !== undefined ? { authz } : {}),
      ...(typeof options.owner === 'string' ? { owner: options.owner } : {}),
      ...(typeof options['root-acl'] === 'string'
        ? { rootAcl: new TextDecoder('utf-8', { fatal: true }).decode(readWhole(options['root-acl'])) }
        : {}),
      realClock: true,
      dir: positional[0]
    })
  } catch (error) {
    if (error instanceof LwsHostError && error.unknownOp) {
      return notWired('lws-serve', error.message)
    }
    // The engine refused to open the storage (a bad configuration, or a
    // snapshot it could not read or authenticate, issue 921), or the state
    // file is not JSON: the message is the whole answer.
    if (error !== null && typeof error === 'object' &&
        (error.envelope !== undefined || error.stateFile === true)) {
      err(`factoidal lws-serve: ${error.envelope !== undefined ? error.envelope.error : error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  // The engine's start notices (a stale lock taken over; encryption at rest
  // on or off), printed also with --quiet.
  for (const n of (await running.storage()).notices || []) err(`lws-serve: ${n}`)
  if (!quiet) {
    err(`lws-serve: listening on ${running.origin} for ${positional[0]}`)
    if (running.authz() !== null) err(`lws-serve: authorization server ${running.authz().issuer} (keys in ${authzDir})`)
    if (options['allow-http'] === true) err('lws-serve: WARNING: --allow-http: http subject identifiers are accepted')
    if (options['allow-private-fetch'] === true) err('lws-serve: WARNING: --allow-private-fetch: private addresses may be fetched')
    if (insecure) {
      err('lws-serve: WARNING: --insecure-no-auth: every request is served without authorization')
      err('lws-serve: --insecure-no-auth: only the Host names of this listener are answered, and a ' +
        'request that changes state from another origin is refused (issue 1124; add names with ' +
        '--allow-host, origins with --allow-origin)')
      if (options['cors-origin'] === undefined) {
        err('lws-serve: --insecure-no-auth: no CORS fields are sent, because with no authorization ' +
          'an echoed Origin would let any web page read and write this storage; give --cors-origin ' +
          'ORIGIN for each page that may use it (https://github.com/danbri/factoidal/issues/1124)')
      }
    }
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

async function commandAuthzServe (positional, options) {
  if (positional.length !== 1) throw new UsageError('authz-serve needs one DIR')
  if (typeof options.resource !== 'string') {
    throw new UsageError('authz-serve needs --resource IRI[,IRI...]: the resources tokens may be issued for')
  }
  const quiet = options.quiet === true
  const { listen } = await import('../authz/server.mjs')
  let running
  try {
    running = await listen({
      port: servePort(options, 3001),
      host: serveHost(options),
      dir: positional[0],
      resources: options.resource.split(',').filter((v) => v !== ''),
      ...(typeof options.issuer === 'string' ? { issuer: options.issuer } : {}),
      // Passed unread; the engine checks them (Wasm/Ops/Authz.lean).
      ...(typeof options.alg === 'string' ? { alg: options.alg } : {}),
      ...(options['token-lifetime'] !== undefined ? { tokenLifetime: natOption('token-lifetime', options['token-lifetime']) } : {}),
      ...(options['rotate-after'] !== undefined ? { rotateAfter: natOption('rotate-after', options['rotate-after']) } : {}),
      ...(options['allow-http'] === true ? { allowHttp: true } : {}),
      ...(options['allow-private-fetch'] === true ? { allowPrivateFetch: true } : {}),
      ...corsConfig(options),
      ...samlConfig(options)
    })
  } catch (error) {
    if (error !== null && typeof error === 'object' && error.envelope !== undefined) {
      err(`factoidal authz-serve: ${error.envelope.error}`)
      return EXIT_FAILURE
    }
    if (error !== null && typeof error === 'object' && /unknown op/.test(String(error.message))) {
      return notWired('authz-serve', error.message)
    }
    throw error
  }
  if (!quiet) {
    err(`authz-serve: listening on ${running.origin}, issuer ${running.issuer}`)
    if (options['allow-http'] === true) err('authz-serve: WARNING: --allow-http: http subject identifiers are accepted')
    if (options['allow-private-fetch'] === true) err('authz-serve: WARNING: --allow-private-fetch: private addresses may be fetched')
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

// lws-keygen (https://github.com/danbri/factoidal/issues/1135): 32 random
// bytes from the host's random source go to the engine (`lwsStorageKeyNew`),
// which gives the key text and its key id. The key goes to standard output
// only; nothing is written to a file.
async function commandLwsKeygen (positional, options) {
  if (positional.length !== 0) throw new UsageError('lws-keygen takes no argument')
  const random = new Uint8Array(32)
  globalThis.crypto.getRandomValues(random)
  const engine = await loadEngine()
  let res
  try {
    res = engine.call('lwsStorageKeyNew', [JSON.stringify({ random: Buffer.from(random).toString('base64') })])
  } catch (error) {
    const message = error && error.message ? String(error.message) : String(error)
    if (message.indexOf('unknown op') >= 0) return notWired('lws-keygen', message)
    throw error
  }
  if (res.ok === false) {
    err(`factoidal lws-keygen: ${res.error}`)
    return EXIT_FAILURE
  }
  if (options.json === true) {
    out(JSON.stringify({ key: res.key, keyId: res.keyId }))
  } else {
    out(res.key)
    if (options.quiet !== true) {
      err(`lws-keygen: key id ${res.keyId}. Keep a copy of the key in a safe place: without it the storage cannot be read.`)
      err('lws-keygen: start the server with FACTOIDAL_LWS_KEY set to it, on an empty storage directory.')
    }
  }
  return EXIT_OK
}

async function commandAuthzKeys (positional, options) {
  if (positional.length !== 1) throw new UsageError('authz-keys needs one DIR')
  const { openAuthorizationServer, readKeyFile } = await import('../authz/server.mjs')
  if (readKeyFile(positional[0]) === null) {
    err(`factoidal authz-keys: ${positional[0]} holds no key file`)
    return EXIT_FAILURE
  }
  let authz
  try {
    // The issuer and resources do not matter for reading the keys.
    authz = await openAuthorizationServer({ dir: positional[0], issuer: 'https://authz.invalid', resources: [] })
  } catch (error) {
    if (error !== null && typeof error === 'object' && error.envelope !== undefined) {
      err(`factoidal authz-keys: ${error.envelope.error}`)
      return EXIT_FAILURE
    }
    throw error
  }
  try {
    if (options.private === true) {
      out(JSON.stringify(authz.privateJwks()))
    } else {
      const answer = await authz.step({ method: 'GET', target: '/jwks', headers: [], body: '' })
      out(answer.body)
    }
  } finally {
    authz.close()
  }
  return EXIT_OK
}

async function commandSolidServe (positional, options) {
  if (positional.length !== 1) throw new UsageError('solid-serve needs one DIR')
  const quiet = options.quiet === true
  // The same rule as lws-serve: no start without a trusted issuer unless
  // the development mode is asked for by name.
  const insecure = options['insecure-no-auth'] === true
  const issuerOption = typeof options.issuer === 'string' ? options.issuer : null
  const authFile = typeof options['auth-config'] === 'string' ? options['auth-config'] : null
  if (!insecure && issuerOption === null && authFile === null) {
    throw new UsageError('solid-serve needs --issuer IRI or --auth-config FILE, ' +
      'or --insecure-no-auth for development')
  }
  if (insecure && (issuerOption !== null || authFile !== null)) {
    throw new UsageError('--insecure-no-auth cannot be combined with --issuer or --auth-config')
  }
  if (!insecure && hasLocalGuardOptions(options)) {
    throw new UsageError('--allow-host and --allow-origin go with --insecure-no-auth; under authentication the token decides')
  }
  let auth
  if (authFile !== null) {
    auth = readJsonFile(authFile)
  } else if (issuerOption !== null) {
    auth = { issuers: issuerOption.split(',').filter((v) => v !== '').map((issuer) => ({ issuer })) }
  }
  const { listen, SolidServerHostError } = await import('../solid/server/index.mjs')
  let running
  try {
    running = await listen({
      port: servePort(options, 3000),
      host: serveHost(options),
      ...(typeof options.base === 'string' ? { baseIri: options.base } : {}),
      ...(insecure ? { insecureNoAuth: true, ...localGuardConfig(options) } : { auth }),
      ...(typeof options.owner === 'string' ? { owner: options.owner } : {}),
      realClock: true,
      dir: positional[0]
    })
  } catch (error) {
    if (error instanceof SolidServerHostError && error.unknownOp) {
      return notWired('solid-serve', error.message)
    }
    // The engine refused to open the storage (a bad configuration, or a
    // snapshot it could not read or authenticate, issue 921), or the state
    // file is not JSON: the message is the whole answer.
    if (error !== null && typeof error === 'object' &&
        (error.envelope !== undefined || error.stateFile === true)) {
      err(`factoidal solid-serve: ${error.envelope !== undefined ? error.envelope.error : error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  // The engine's start notices (a stale lock taken over; encryption at rest
  // on or off), printed also with --quiet.
  for (const n of (await running.storage()).notices || []) err(`solid-serve: ${n}`)
  if (!quiet) {
    err(`solid-serve: listening on ${running.origin} for ${positional[0]}`)
    if (insecure) {
      err('solid-serve: WARNING: --insecure-no-auth: every request is served without authentication')
      err('solid-serve: --insecure-no-auth: only the Host names of this listener are answered, and a ' +
        'request that changes state from another origin is refused (issue 1124; add names with ' +
        '--allow-host, origins with --allow-origin). CORS still echoes the request Origin (Solid ' +
        'Protocol section 8.1), so a page on another origin can read this storage ' +
        '(https://github.com/danbri/factoidal/issues/1124)')
    }
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

// webdav-serve CONFIGDIR (https://github.com/danbri/factoidal/issues/1066):
// the host carries sockets, files and fetches; the engine reads the mount
// files and decides every answer (L4Factoidal/WebDAV/).
async function commandWebdavServe (positional, options) {
  if (positional.length !== 1) throw new UsageError('webdav-serve needs one CONFIGDIR')
  const quiet = options.quiet === true
  if (options.xmpp !== undefined) return webdavOverXmpp(positional[0], options, quiet)
  const { listen, WebdavHostError } = await import('../webdav/server.mjs')
  const fs = await import('node:fs/promises')
  const { resolve: resolvePath } = await import('node:path')
  const useTls = options.cert !== undefined || options.key !== undefined
  if (useTls && (typeof options.cert !== 'string' || typeof options.key !== 'string')) {
    throw new UsageError('--cert and --key go together')
  }
  const settings = { configDir: positional[0], port: servePort(options, 8090), host: serveHost(options) }
  // The users file is named relative to the working directory here, and
  // given to the engine as an absolute path.
  if (typeof options.users === 'string') settings.users = resolvePath(options.users)
  // The Host and Origin guard (https://github.com/danbri/factoidal/issues/1124):
  // the values go to the engine unread; it checks them.
  Object.assign(settings, localGuardConfig(options))
  // The failed-login limit (https://github.com/danbri/factoidal/issues/1119):
  // the values go to the engine unread; it checks them.
  if (options['login-limit'] !== undefined) settings.loginLimit = String(options['login-limit'])
  if (options['login-window'] !== undefined) settings.loginWindow = String(options['login-window'])
  if (options['dangerously-disable-ratelimits'] !== undefined) {
    settings.disableRateLimits = options['dangerously-disable-ratelimits'] === true
  }
  let running
  try {
    if (useTls) {
      settings.cert = await fs.readFile(options.cert)
      settings.key = await fs.readFile(options.key)
    }
    running = await listen(settings)
  } catch (error) {
    if (error instanceof WebdavHostError && error.unknownOp) return notWired('webdav-serve', error.message)
    if (error instanceof WebdavHostError || (error !== null && typeof error === 'object' && error.code === 'ENOENT')) {
      err(`factoidal webdav-serve: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  // The engine's start warnings (--dangerously-disable-ratelimits), printed
  // also with --quiet.
  for (const w of running.warnings || []) err(`factoidal webdav-serve: WARNING: ${w}`)
  // The start notices of the local mounts (a stale lock taken over;
  // encryption at rest on or off), printed also with --quiet.
  for (const n of running.storageNotices || []) err(`webdav-serve: ${n}`)
  if (!quiet) {
    err(`webdav-serve: listening on ${running.origin} for ${positional[0]}` +
        (settings.users !== undefined ? `, login from ${options.users}` : ', NO LOGIN on this listener') +
        (useTls ? ', TLS' : ''))
    for (const m of running.mounts) {
      err(`webdav-serve: ${running.origin}/${encodeURIComponent(m.name)}/ - ${m.title} (${m.kind}${m.writable ? '' : ', read-only'}${m.agent ? ', as ' + m.agent : ''})`)
    }
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

// webdav-serve CONFIGDIR --xmpp JID (https://github.com/danbri/factoidal/issues/1107,
// step 1): the WebDAV handle of the HTTP listener, reached through an
// outgoing XMPP client connection (XEP-0332). No port is opened. The host
// moves bytes; the stream, SASL, binding, access and every response stanza
// are decided in L4Factoidal/XMPP/ (ClientStream, HttpOverXmpp).
async function webdavOverXmpp (configDir, options, quiet) {
  if (typeof options.xmpp !== 'string') throw new UsageError('--xmpp needs a JID')
  if (typeof options['xmpp-password-file'] !== 'string') throw new UsageError('--xmpp needs --xmpp-password-file FILE')
  if (typeof options['xmpp-allow'] !== 'string') throw new UsageError('--xmpp needs --xmpp-allow JID[,JID...]')
  // No login on the XMPP path yet: refuse --users rather than ignore it
  // (https://github.com/danbri/factoidal/issues/1125).
  if (['users', 'cert', 'key', 'login-limit', 'login-window', 'dangerously-disable-ratelimits'].some((k) => options[k] !== undefined)) {
    throw new UsageError('--users, --cert, --key and the login-limit options do not apply with --xmpp yet (https://github.com/danbri/factoidal/issues/1125)')
  }
  const fs = await import('node:fs/promises')
  const password = (await fs.readFile(options['xmpp-password-file'], 'utf8')).split(/\r?\n/)[0]
  const allow = options['xmpp-allow'].split(',').map((x) => x.trim()).filter((x) => x.length > 0)
  const { openWebdav, WebdavHostError } = await import('../webdav/server.mjs')
  const { connectHttpTarget, XmppClientError } = await import('../xmpp/client.mjs')
  let dav
  try {
    dav = await openWebdav({ configDir })
  } catch (error) {
    if (error instanceof WebdavHostError && error.unknownOp) return notWired('webdav-serve', error.message)
    if (error instanceof WebdavHostError || (error !== null && typeof error === 'object' && error.code === 'ENOENT')) {
      err(`factoidal webdav-serve: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  for (const n of dav.storageNotices || []) err(`webdav-serve: ${n}`)
  const settings = {
    engine: dav.engine,
    jid: options.xmpp,
    password,
    allow,
    resource: typeof options['xmpp-resource'] === 'string' ? options['xmpp-resource'] : 'dav',
    tls: options['xmpp-tls'] === true,
    mounts: dav.mounts,
    dangerouslyAllowWritableWithoutLogin: options['dangerously-allow-writable-without-login'] === true,
    step: (request) => dav.step(request),
    onError: (error) => { if (!quiet) err(`webdav-serve: xmpp: ${error.message}`) }
  }
  if (typeof options['xmpp-host'] === 'string') settings.host = options['xmpp-host']
  if (typeof options['xmpp-ca'] === 'string') settings.tlsOptions = { ca: await fs.readFile(options['xmpp-ca']) }
  if (options['xmpp-port'] !== undefined) {
    const port = Number(options['xmpp-port'])
    if (!Number.isInteger(port) || port < 1 || port > 65535) throw new UsageError('--xmpp-port needs a port number')
    settings.port = port
  }
  let conn
  try {
    conn = await connectHttpTarget(settings)
  } catch (error) {
    dav.close()
    if (error instanceof XmppClientError && error.unknownOp) return notWired('webdav-serve', error.message)
    if (error instanceof XmppClientError || (error !== null && typeof error === 'object' && typeof error.code === 'string')) {
      err(`factoidal webdav-serve: xmpp: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  if (!quiet) {
    err(`webdav-serve: connected to XMPP as ${conn.jid}; no port is open; requests from ${allow.join(', ')}`)
    if (conn.writableWithoutLogin.length > 0) {
      err(`webdav-serve: WARNING: --dangerously-allow-writable-without-login: every allowed JID can write ${conn.writableWithoutLogin.join(', ')} as the storage owner, with no login`)
    }
    for (const m of dav.mounts) {
      err(`webdav-serve: /${encodeURIComponent(m.name)}/ - ${m.title} (${m.kind}${m.writable ? '' : ', read-only'}${m.agent ? ', as ' + m.agent : ''})`)
    }
  }
  out(`xmpp:${conn.jid}`)
  const running = { close: async () => { await conn.close(); dav.close() } }
  const ended = conn.closed.then((reason) => {
    if (!quiet && reason) err(`webdav-serve: xmpp: connection closed: ${reason}`)
    dav.close()
    return EXIT_FAILURE
  })
  return Promise.race([untilInterrupted(running, quiet), ended])
}

// xmpp-http-proxy (https://github.com/danbri/factoidal/issues/1107, step 2):
// a loopback HTTP listener whose requests go over XMPP (XEP-0332) to one
// target JID. The host moves bytes; the target, the listener address, the
// headers forwarded, the limits, timeouts and every status are decided in
// L4Factoidal/XMPP/HttpRequester.lean and Wasm/Ops/XmppClient.lean.
async function commandXmppHttpProxy (positional, options) {
  if (positional.length !== 0) throw new UsageError('xmpp-http-proxy takes no positional argument')
  const quiet = options.quiet === true
  if (typeof options.xmpp !== 'string') throw new UsageError('xmpp-http-proxy needs --xmpp JID')
  if (typeof options['xmpp-password-file'] !== 'string') throw new UsageError('xmpp-http-proxy needs --xmpp-password-file FILE')
  if (typeof options.target !== 'string') throw new UsageError('xmpp-http-proxy needs --target JID/RESOURCE')
  const fs = await import('node:fs/promises')
  const password = (await fs.readFile(options['xmpp-password-file'], 'utf8')).split(/\r?\n/)[0]
  const { startHttpProxy } = await import('../xmpp/proxy.mjs')
  const { XmppClientError } = await import('../xmpp/client.mjs')
  const settings = {
    jid: options.xmpp,
    password,
    target: options.target,
    resource: typeof options['xmpp-resource'] === 'string' ? options['xmpp-resource'] : 'proxy',
    tls: options['xmpp-tls'] === true,
    // The address goes to the engine unread; it accepts 127.0.0.1 only.
    listenHost: typeof options.host === 'string' ? options.host : '127.0.0.1',
    listenPort: servePort(options, 8091),
    onError: (error) => { if (!quiet) err(`xmpp-http-proxy: ${error.message}`) }
  }
  if (options.timeout !== undefined) {
    const t = Number(options.timeout)
    if (!Number.isInteger(t) || t < 0) throw new UsageError('--timeout needs a whole number of seconds')
    settings.timeoutSeconds = t
  }
  if (typeof options['xmpp-host'] === 'string') settings.host = options['xmpp-host']
  if (typeof options['xmpp-ca'] === 'string') settings.tlsOptions = { ca: await fs.readFile(options['xmpp-ca']) }
  if (options['xmpp-port'] !== undefined) {
    const port = Number(options['xmpp-port'])
    if (!Number.isInteger(port) || port < 1 || port > 65535) throw new UsageError('--xmpp-port needs a port number')
    settings.port = port
  }
  let running
  try {
    running = await startHttpProxy(settings)
  } catch (error) {
    if (error instanceof XmppClientError && error.unknownOp) return notWired('xmpp-http-proxy', error.message)
    if (error instanceof XmppClientError || (error !== null && typeof error === 'object' && typeof error.code === 'string')) {
      err(`factoidal xmpp-http-proxy: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
  if (!quiet) {
    err(`xmpp-http-proxy: connected to XMPP as ${running.jid}; requests to ${running.origin} go to ${running.target} only`)
    err('xmpp-http-proxy: the listener has no login: every local process (and any web page in a local browser) acts as ' +
        `${running.jid} (https://github.com/danbri/factoidal/issues/1124)`)
  }
  out(running.origin)
  const ended = running.closed.then((reason) => {
    if (!quiet && reason) err(`xmpp-http-proxy: xmpp: connection closed: ${reason}`)
    return EXIT_FAILURE
  })
  return Promise.race([untilInterrupted(running, quiet), ended])
}

/** A password from standard input: on a terminal, asked for with no echo;
 *  else all of standard input. The bytes go to the engine unread. Pure I/O. */
async function readPasswordInput () {
  const stdin = process.stdin
  if (!stdin.isTTY) {
    const chunks = []
    for await (const chunk of stdin) chunks.push(chunk)
    return new Uint8Array(Buffer.concat(chunks))
  }
  process.stderr.write('Password: ')
  stdin.setRawMode(true)
  stdin.resume()
  const typed = []
  try {
    for await (const chunk of stdin) {
      for (const b of chunk) {
        if (b === 0x0d || b === 0x0a || b === 0x04) return new Uint8Array(typed)
        if (b === 0x03) throw new UsageError('interrupted')
        if (b === 0x7f || b === 0x08) typed.pop()
        else typed.push(b)
      }
    }
    return new Uint8Array(typed)
  } finally {
    stdin.setRawMode(false)
    stdin.pause()
    err('')
  }
}

// webdav-user FILE NAME (https://github.com/danbri/factoidal/issues/1108):
// the engine checks the name, the password and the file, names the PBKDF2
// derivation, and gives the new text; this host reads the password, runs
// the derivation with WebCrypto (lib/cipher-host.mjs) and writes the file.
async function commandWebdavUser (positional, options) {
  if (positional.length !== 2) throw new UsageError('webdav-user needs FILE and NAME')
  const [file, name] = positional
  const fs = await import('node:fs')
  const { dirname, basename, join } = await import('node:path')
  const { runWithCipher } = await import('../lib/cipher-host.mjs')
  let text = null
  try {
    text = fs.readFileSync(file, 'utf8')
  } catch (error) {
    if (error === null || typeof error !== 'object' || error.code !== 'ENOENT') throw error
  }
  const input = await readPasswordInput()
  const salt = new Uint8Array(16)
  globalThis.crypto.getRandomValues(salt)
  const engine = await loadEngine()
  const args = {
    name,
    file,
    text,
    passwordBase64: Buffer.from(input).toString('base64'),
    saltBase64: Buffer.from(salt).toString('base64')
  }
  if (options.iterations !== undefined) args.iterations = String(options.iterations)
  let res
  try {
    res = await runWithCipher((a) => engine.call('webdavUser', [JSON.stringify(a)]), args)
  } catch (error) {
    const message = error && error.message ? String(error.message) : String(error)
    if (message.indexOf('unknown op') >= 0) return notWired('webdav-user', message)
    throw error
  }
  if (res.ok === false) {
    err(`factoidal webdav-user: ${res.error}`)
    return EXIT_FAILURE
  }
  // A new file in the same directory, mode 0600, flushed, renamed over FILE.
  const temp = join(dirname(file), `.${basename(file)}.${process.pid}.tmp`)
  const fd = fs.openSync(temp, 'wx', 0o600)
  try {
    fs.writeSync(fd, res.text)
    fs.fsyncSync(fd)
  } finally {
    fs.closeSync(fd)
  }
  fs.renameSync(temp, file)
  err(`webdav-user: ${res.replaced ? 'replaced' : 'added'} ${name} in ${file}`)
  return EXIT_OK
}

async function commandXmppServe (positional, options) {
  if (positional.length !== 1) throw new UsageError('xmpp-serve needs one DIR')
  const quiet = options.quiet === true
  const { listen, XmppHostError } = await import('../xmpp/server.mjs')
  const fs = await import('node:fs/promises')
  const useTls = options.cert !== undefined || options.key !== undefined
  if (useTls && (typeof options.cert !== 'string' || typeof options.key !== 'string')) {
    throw new UsageError('--cert and --key go together')
  }
  const settings = {
    dir: positional[0],
    port: servePort(options, useTls ? 5223 : 5222),
    host: serveHost(options),
    onError: (error) => { if (!quiet) err(`xmpp-serve: ${error.message}`) }
  }
  if (typeof options.domain === 'string') settings.domain = options.domain
  if (typeof options.accounts === 'string') settings.accountsText = await fs.readFile(options.accounts, 'utf8')
  if (useTls) {
    settings.cert = await fs.readFile(options.cert)
    settings.key = await fs.readFile(options.key)
  }
  let running
  try {
    running = await listen(settings)
  } catch (error) {
    if (error instanceof XmppHostError && error.unknownOp) {
      return notWired('xmpp-serve', error.message)
    }
    throw error
  }
  if (!quiet) {
    err(`xmpp-serve: listening on ${running.origin} for domain ${running.xmpp.domain}` +
        ` (${running.xmpp.accounts} accounts, state ${positional[0]}` +
        (useTls ? ', direct TLS)' : ', PLAINTEXT: no TLS on this listener)'))
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
}

// The command's verbs, as aliases for the wasm ABI's request kinds. A
// kind name is accepted directly too, so this table adds a spelling and
// hides nothing.
const SOLID_CLIENT_ALIASES = {
  get: 'read',
  put: 'replace',
  post: 'create',
  delete: 'delete',
  discover: 'discoverStorage'
}

async function commandSolidClient (positional, options) {
  if (positional.length !== 2) {
    throw new UsageError('solid-client needs an operation and a URL')
  }
  const [verb, target] = positional
  const { createSolidClient, SolidClientHostError, SOLID_REQUEST_KINDS } =
    await import('../solid/client/index.mjs')
  const kind = Object.prototype.hasOwnProperty.call(SOLID_CLIENT_ALIASES, verb)
    ? SOLID_CLIENT_ALIASES[verb]
    : verb
  if (!SOLID_REQUEST_KINDS.includes(kind)) {
    throw new UsageError(
      `unknown operation "${verb}"; one of ` +
      `${Object.keys(SOLID_CLIENT_ALIASES).join(', ')} or ` +
      `${SOLID_REQUEST_KINDS.join(', ')}`)
  }
  const args = { target }
  if (typeof options.file === 'string') {
    args.body = new TextDecoder('utf-8', { fatal: true }).decode(readWhole(options.file))
  } else if (typeof options.body === 'string') {
    args.body = options.body
  }
  if (typeof options['content-type'] === 'string') {
    args.contentType = options['content-type']
  }
  if (['create', 'replace', 'patch'].includes(kind) && args.body === undefined) {
    throw new UsageError(`${verb} needs --body or --file`)
  }
  const extra = typeof options.interpret === 'string'
    ? { interpret: options.interpret }
    : {}
  let answer
  try {
    const client = await createSolidClient()
    answer = await client.run(kind, args, extra)
  } catch (error) {
    if (error instanceof SolidClientHostError && error.unknownOp) {
      return notWired('solid-client', error.message)
    }
    throw error
  }
  out(JSON.stringify(answer, null, 2))
  return EXIT_OK
}

// `factoidal lws-client`: the caller's options become the members of one
// operation document; the engine decides everything else.
async function commandLwsClient (positional, options) {
  if (positional.length !== 2) {
    throw new UsageError('lws-client needs an operation and a URL')
  }
  const [kind, url] = positional
  const { createLwsClient, LwsClientError, LWS_CLIENT_KINDS } = await import('../lws/client.mjs')
  if (!LWS_CLIENT_KINDS.includes(kind) || kind === 'verifyNotification') {
    throw new UsageError(`unknown operation "${kind}"; one of ` +
      LWS_CLIENT_KINDS.filter((k) => k !== 'verifyNotification').join(', '))
  }
  const list = (v) => String(v).split(',').filter((x) => x !== '')
  const op = { kind, url }
  if (typeof options.file === 'string') op.body = readWhole(options.file)
  else if (typeof options.body === 'string') op.body = options.body
  if (typeof options['content-type'] === 'string') op.mediaType = options['content-type']
  if (typeof options.slug === 'string') op.slug = options.slug
  if (options.container === true) op.container = true
  if (options.recursive === true) op.recursive = true
  if (typeof options.type === 'string') op.types = list(options.type)
  if (typeof options.link === 'string') op.links = [options.link]
  if (typeof options['if-match'] === 'string') { op.precondition = 'ifMatch'; op.tag = options['if-match'] }
  if (options['if-match-current'] === true) op.precondition = 'ifMatchCurrent'
  if (options['if-none-match-star'] === true) op.precondition = 'ifNoneMatchStar'
  if (typeof options['if-unmodified-since'] === 'string') {
    op.precondition = 'ifUnmodifiedSince'; op.tag = options['if-unmodified-since']
  }
  if (options['no-precondition'] === true) op.precondition = 'none'
  if (typeof options['if-none-match'] === 'string') {
    // The value goes to the engine whole; it reads the entity-tag list.
    if (kind === 'read') op.ifNoneMatch = options['if-none-match']
    else op.ifNoneMatchTags = [options['if-none-match']]
  }
  if (typeof options['retry-412'] === 'string') op.retry412 = Number(options['retry-412'])
  if (typeof options.destination === 'string') op.destination = options.destination
  if (typeof options.query === 'string') op.query = JSON.parse(options.query)
  if (typeof options.topic === 'string') op.topics = list(options.topic)
  if (typeof options.inbox === 'string') op.inbox = options.inbox
  if (typeof options.action === 'string') op.actions = list(options.action)
  if (typeof options.assignee === 'string') op.assignee = options.assignee
  if (typeof options.target === 'string') op.targets = list(options.target)
  if (typeof options.policies === 'string') op.policies = JSON.parse(options.policies)
  if (typeof options.endpoint === 'string') op.endpoint = options.endpoint
  const clientOptions = {}
  if (options['legacy-challenge'] === true) clientOptions.legacyChallenge = true
  if (options['require-https'] === true) clientOptions.requireHttps = true
  if (typeof options['subject-token-file'] === 'string') {
    clientOptions.subjectToken = new TextDecoder('utf-8', { fatal: true })
      .decode(readWhole(options['subject-token-file'])).trim()
  }
  if (typeof options['subject-token-type'] === 'string') {
    clientOptions.subjectTokenType = options['subject-token-type']
  }
  if (typeof options['access-token'] === 'string') {
    if (typeof options.storage !== 'string' || typeof options.root !== 'string') {
      throw new UsageError('--access-token needs --storage IRI and --root URL')
    }
    clientOptions.session = {
      tokens: [{ storage: options.storage, root: options.root, token: options['access-token'] }]
    }
  }
  let answer
  try {
    const client = await createLwsClient(clientOptions)
    answer = await client.run(op)
  } catch (error) {
    if (error instanceof LwsClientError) {
      if (error.unknownOp) return notWired('lws-client', error.message)
      out(JSON.stringify({ fail: error.detail }, null, 2))
      return EXIT_FAILURE
    }
    throw error
  }
  out(JSON.stringify(answer, null, 2))
  return EXIT_OK
}

const COMMANDS = {
  version: (positional, options) => commandVersion(options),
  'sample-store': (positional, options) => commandSampleStore(positional, options),
  inspect: commandInspect,
  query: commandQuery,
  pack: commandPack,
  activate: commandActivate,
  update: commandUpdate,
  compact: commandCompact,
  serve: commandServe,
  'lws-serve': commandLwsServe,
  'solid-serve': commandSolidServe,
  'solid-client': commandSolidClient,
  'lws-client': commandLwsClient,
  'authz-serve': commandAuthzServe,
  'authz-keys': commandAuthzKeys,
  'xmpp-serve': commandXmppServe,
  'webdav-serve': commandWebdavServe,
  'webdav-user': commandWebdavUser,
  'xmpp-http-proxy': commandXmppHttpProxy,
  'lws-keygen': commandLwsKeygen
}

// ----------------------------------------------------------------- main

async function main () {
  if (argv.length === 0) {
    out(REVIEW_WARNING + '\n')
    out(USAGE)
    return EXIT_USAGE
  }
  const command = argv[0]
  if (command === '--help' || command === '-h' || command === 'help') {
    const topic = argv[1]
    out(REVIEW_WARNING + '\n')
    if (typeof topic === 'string' && Object.prototype.hasOwnProperty.call(COMMAND_USAGE, topic)) {
      out(COMMAND_USAGE[topic])
    } else {
      out(USAGE)
    }
    return EXIT_OK
  }
  if (command === '--version') return commandVersion({})
  if (!Object.prototype.hasOwnProperty.call(COMMANDS, command)) {
    err(`factoidal: unknown command "${command}"`)
    err(USAGE)
    return EXIT_USAGE
  }
  let parsed
  try {
    parsed = parseArguments(argv.slice(1), VALUE_OPTIONS[command])
  } catch (error) {
    if (error instanceof UsageError) {
      err(`factoidal ${command}: ${error.message}`)
      return EXIT_USAGE
    }
    throw error
  }
  if (parsed.options.help) {
    out(REVIEW_WARNING + '\n')
    out(COMMAND_USAGE[command])
    return EXIT_OK
  }
  if (WARNED_COMMANDS.has(command)) {
    err(`factoidal ${command}: WARNING: ${REVIEW_WARNING}`)
  }
  try {
    return await COMMANDS[command](parsed.positional, parsed.options)
  } catch (error) {
    if (error instanceof UsageError) {
      err(`factoidal ${command}: ${error.message}`)
      err('')
      err(COMMAND_USAGE[command])
      return EXIT_USAGE
    }
    if (error instanceof StoreHostError) {
      err(`factoidal ${command}: ${error.code}: ${error.message}`)
      return EXIT_FAILURE
    }
    if (error instanceof StoreOperationError) {
      err(`factoidal ${command}: ${error.message}`)
      return EXIT_FAILURE
    }
    throw error
  }
}

exit(await main())
