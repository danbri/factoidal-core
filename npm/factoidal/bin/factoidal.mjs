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

const EXIT_OK = 0
const EXIT_FAILURE = 1
const EXIT_USAGE = 2
const EXIT_NOT_WIRED = 3

// Progress is reported about every 16 MiB; the packer feeds 65,536 bytes
// a time, so this is the window that catches one feed per report.
const FEED_PROGRESS = 65536

const PACK_LAYOUTS = ['ibk3', 'ibk4', 'ibk5']
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
  solid-client OP URL         run one Solid client operation

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
  --layout LAYOUT    ibk3 (triples, default), ibk4 (quads, wire version 9)
                     or ibk5 (quads, wire version 10: RDF 1.2 terms,
                     out-of-line literals, zone maps)
  --syntax SYNTAX    turtle, trig or nquads; default from the file extension
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
verification never becomes current.`,

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

An update, or a Graph Store PUT, POST or DELETE, is appended to the
activated generation's delta log as one batch before the response is sent,
and is visible to the next request. An IBK3 (triples) generation accepts
changes to the default graph only, because its delta log is replayed and
compacted for that graph only; a change to a named graph answers 501. A
quad generation (ibk4, ibk5) accepts every graph. Fold the log into a new
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

  'lws-serve': `factoidal lws-serve - serve Linked Web Storage 1.0 over HTTP

usage: factoidal lws-serve DIR (--issuer IRI | --auth-config FILE | --insecure-no-auth)
                         [--owner WEBID] [--root-acl FILE] [--audience IRI]
                         [--port N] [--host ADDRESS] [--base IRI]

Starts a Node HTTP server that answers every request through the engine's
lwsStep operation.

DIR names the storage directory. The storage is kept in the engine
handle and written to DIR/lws-state.json after every request that
changed it (temporary file, fsync, rename), and read back on the next
start. The engine decides the snapshot format and refuses a snapshot
path with a dot segment or other traversal form
(formal/lean4/L4Factoidal/LWS/Snapshot.lean).

  --port N        the port to bind; 0 takes an ephemeral one (default 3000)
  --host ADDRESS  the address to bind (default 127.0.0.1)
  --base IRI      the absolute IRI the storage root maps to
                  (default: the bound origin)

Authorization (LWS editor's draft, section Authorization; one of the three
is required):
  --issuer IRI          trust this authorization server; several may be
                        given separated by commas. Its metadata is read from
                        IRI/.well-known/lws-configuration and its keys from
                        the jwks_uri there, when a token first needs them.
  --auth-config FILE    the engine's "auth" configuration as JSON:
                        {"issuers":[{"issuer":IRI,"jwks":{...}?}],
                         "audience":IRI?, "leeway":SECONDS?,
                         "refreshInterval":SECONDS?}
  --insecure-no-auth    development only: no authorization at all; every
                        request is served. Never the default.
  --owner WEBID         the storage owner: a new storage gets a root ACL
                        that gives this agent Read, Write and Control
  --root-acl FILE       a Turtle root ACL for a new storage instead
  --audience IRI        the aud value tokens must carry (default: the
                        storage root IRI)

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
                  Control is not enforced

The server makes no protocol decision. Storage discovery, containment
triples, slash semantics, the Allow and Accept-* headers, the PUT/POST/
PATCH/DELETE rules, the acl and describedby lifecycle, N3 Patch, Web
Access Control, CORS and the LDN inbox are answered by
formal/lean4/L4Factoidal/Solid/Server/. A WebAssembly module built before
those operations landed makes this command exit 3 and say so.

Specification: https://solidproject.org/TR/protocol`,

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

Specification: https://solidproject.org/TR/protocol`
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
    if (equals >= 0) {
      options[name] = argument.slice(equals + 1)
      continue
    }
    if (valueOptions.has(name)) {
      index += 1
      if (index >= args.length) {
        throw new UsageError(`option --${name} needs a value`)
      }
      options[name] = args[index]
      continue
    }
    options[name] = true
  }
  return { positional, options }
}

class UsageError extends Error {}

const VALUE_OPTIONS = {
  version: new Set([]),
  'sample-store': new Set([]),
  inspect: new Set(['generation']),
  query: new Set(['query', 'file', 'format', 'limit', 'base', 'generation']),
  pack: new Set(['layout', 'syntax', 'chunk-bytes', 'base', 'batch-bytes']),
  activate: new Set([]),
  update: new Set(['update', 'file']),
  compact: new Set([]),
  serve: new Set(['port', 'host', 'query-path', 'gsp-path', 'file', 'layout', 'tdb2']),
  'lws-serve': new Set(['port', 'host', 'base', 'issuer', 'auth-config', 'owner', 'root-acl',
    'audience']),
  'solid-serve': new Set(['port', 'host', 'base', 'owner', 'issuer', 'auth-config']),
  'solid-client': new Set(['body', 'file', 'content-type', 'interpret'])
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

// ------------------------------------------------------------- inspect

async function commandInspect (positional, options) {
  if (positional.length !== 1) throw new UsageError('inspect needs exactly one STORE')
  const root = positional[0]
  const named = typeof options.generation === 'string' ? options.generation : null
  const store = openStore(root, named)
  const engine = await loadEngine()
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
  const store = openStore(root, named)
  const engine = await loadEngine()

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
function packSyntax (engine, input, options) {
  const tables = engine.call('engineTables', []).tables
  const syntaxes = tables.packSyntaxes
  if (typeof options.syntax === 'string') {
    const syntax = options.syntax.toLowerCase()
    if (syntaxes.indexOf(syntax) >= 0) return syntax
    throw new UsageError(`--syntax ${options.syntax} is not one of ${syntaxes.join(', ')}`)
  }
  const lower = input.toLowerCase()
  for (const [suffix, syntax] of Object.entries(tables.packSuffixes)) {
    if (lower.endsWith(suffix)) return syntax
  }
  for (const [suffix, name] of Object.entries(tables.packUnsupportedSuffixes)) {
    if (lower.endsWith(suffix)) {
      throw new UsageError(
        `pack does not read ${name}. The packer's streaming fold reads ` +
        `${syntaxes.join(', ')} only. Convert the file first, for ` +
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
function packBase (input, options) {
  if (typeof options.base === 'string') return options.base
  const absolute = input.startsWith('/') ? input : joinPath(currentDirectory(), input)
  return 'file://' + absolute
}

/** The process's working directory, on Node and on Deno. */
function currentDirectory () {
  if (isDeno) return globalThis.Deno.cwd()
  return process.cwd()
}

function packLayout (options) {
  if (typeof options.layout !== 'string') return 'ibk3'
  const layout = options.layout.toLowerCase()
  if (PACK_LAYOUTS.indexOf(layout) >= 0) return layout
  throw new UsageError(`--layout ${options.layout} is not one of ${PACK_LAYOUTS.join(', ')}`)
}

async function commandPack (positional, options) {
  if (positional.length !== 2) throw new UsageError('pack needs INPUT and OUTPUT')
  const [input, output] = positional
  const syntax = packSyntax(await loadEngine(), input, options)
  const layout = packLayout(options)
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
      { kind: 'pack', input, output, syntax, layout, base: packBase(input, options),
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
  out(`${report.written.length} artifacts, ${report.bytesWritten} bytes, layout ${layout}`)
  if (typeof report.rows === 'number') out(`${plural(report.rows, 'row')}`)
  out(`activate it with: factoidal activate ${dirOf(output)} ${nameOf(output)}`)
  return EXIT_OK
}

async function commandSampleStore (positional, options) {
  if (positional.length > 1) throw new UsageError('sample-store takes at most one DIR')
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
    const packOptions = { quiet: true, layout: typeof options.layout === 'string' ? options.layout : 'ibk5' }
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
  const { listen, listenOnWorker, ServeHostError } = await import('./serve.mjs')
  const serveOptions = {
    port: servePort(options, 3030),
    host: serveHost(options),
    ...(tdb2 ? { tdb2: true } : {}),
    ...(typeof options['query-path'] === 'string' ? { queryPath: options['query-path'] } : {}),
    ...(typeof options['gsp-path'] === 'string' ? { gspPath: options['gsp-path'] } : {})
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
  if (!insecure && issuerOption === null && authFile === null) {
    throw new UsageError('lws-serve needs --issuer IRI or --auth-config FILE, ' +
      'or --insecure-no-auth for development')
  }
  if (insecure && (issuerOption !== null || authFile !== null)) {
    throw new UsageError('--insecure-no-auth cannot be combined with --issuer or --auth-config')
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
      ...(insecure ? { insecureNoAuth: true } : { auth }),
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
    throw error
  }
  if (!quiet) {
    err(`lws-serve: listening on ${running.origin} for ${positional[0]}`)
    if (insecure) err('lws-serve: WARNING: --insecure-no-auth: every request is served without authorization')
  }
  out(running.origin)
  return untilInterrupted(running, quiet)
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
      ...(insecure ? { insecureNoAuth: true } : { auth }),
      ...(typeof options.owner === 'string' ? { owner: options.owner } : {}),
      realClock: true,
      dir: positional[0]
    })
  } catch (error) {
    if (error instanceof SolidServerHostError && error.unknownOp) {
      return notWired('solid-serve', error.message)
    }
    throw error
  }
  if (!quiet) {
    err(`solid-serve: listening on ${running.origin} for ${positional[0]}`)
    if (insecure) err('solid-serve: WARNING: --insecure-no-auth: every request is served without authentication')
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
  'solid-client': commandSolidClient
}

// ----------------------------------------------------------------- main

async function main () {
  if (argv.length === 0) {
    out(USAGE)
    return EXIT_USAGE
  }
  const command = argv[0]
  if (command === '--help' || command === '-h' || command === 'help') {
    const topic = argv[1]
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
    out(COMMAND_USAGE[command])
    return EXIT_OK
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
