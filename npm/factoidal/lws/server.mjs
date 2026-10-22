// A Node HTTP host for the Linked Web Storage Protocol 1.0 core.
// https://github.com/danbri/factoidal/issues/659
// Design record: docs/designissues/2026-09-06-lws-and-solid-protocols.md
//
// WHAT THIS FILE IS ALLOWED TO DO
// Accept a socket, turn one HTTP request into the JSON request record,
// call the engine's `lwsStep` on a handle, and write the JSON response
// record back onto the socket. That is the whole contract.
//
// It makes NO protocol decision. It does not choose a status code, does
// not build a `Link` header, does not read or write a resource, does not
// decide whether a PATCH is refused, and does not know what a container
// is. Every one of those lives in `formal/lean4/L4Factoidal/LWS/`
// (iron rule 7 of CLAUDE.md). A reviewer who finds a status code, a
// media type decision or an RDF term in this file has found a rule
// violation. The one status code written here is 500, and only for a
// failure of this host itself.
//
// THE WASM CONTRACT
// Fixed in docs/lws-solid-conformance.md, section "wasm ABI".
//   lwsOpen  [configJson]            -> { ok, handle, root }
//   lwsStep  [handle, requestJson]   -> { ok, response }
//   lwsClose [handle]                -> { ok }
//   lwsFetched [handle, documentJson] -> { ok, fetch? | installed? | refused? }
//   lwsDelivered [handle, reportJson] -> { ok, changed, retry? }
//   lwsFlush [handle, { now? }]       -> { ok, changed, deliveries?, wake? }
//
// RATE LIMIT AND INBOX CHECK (https://github.com/danbri/factoidal/issues/915)
// An answer may carry `wake: SECONDS`: deliveries wait for a rate-limit
// window. This host calls `lwsFlush` after that many seconds and makes the
// deliveries it names. `lwsStep` may answer `{ ok, resolve: { host } }`:
// this host resolves the name (`dns.lookup`, every address) and steps the
// request again with `resolved: [{ host, addresses }]`. The listen address,
// port and the machine's interface addresses go to `lwsOpen` as `listen`.
// Whether an inbox is this server, and how many deliveries go when, are
// decided by `L4Factoidal/LWS/InboxGuard.lean` and `Notifications.lean`.
//
// NOTIFICATIONS (https://github.com/danbri/factoidal/issues/890)
// `lwsStep` may carry `deliveries: [{ id, url, headers, body }]`: HTTP
// requests the engine decided to make (LWS notifications, webhook suite).
// This host POSTs each one exactly as given, after the response to the
// request that caused it, and reports the status it got (0 when no answer
// came) to `lwsDelivered`. When the engine answers `retry`, this host
// waits the number of seconds it names and makes that request. Which
// changes are announced, to whom, with which body and signature, whether
// to retry and when a subscription ends are all decided by
// `formal/lean4/L4Factoidal/LWS/Notifications.lean`.
//
// `lwsStep` may answer `{ ok, fetch: { issuer, url } }` instead of a
// response: the engine needs an authorization server's metadata or key
// set before it can decide. This host fetches that URL, passes
// `{ issuer, url, status, body, now }` to `lwsFetched`, follows any
// further `fetch` it names, and steps the request again.
//
//   request  { method, target, headers: [[name, value]] } + content bytes
//   response { status, headers: [[name, value]], bodyBytes } + content bytes
//
// Bodies are BYTES (https://github.com/danbri/factoidal/issues/889). The
// step goes through the engine's byte-region entry, `callBlobIO`: the
// request content is the IN region and the response content is the OUT
// region, with no encoding and no decoding here. This host never reads a
// body as text.
//
// The config members are `baseIri`, `now`, `owner`, `agent`, `pageSize`, `rootAcl`,
// `auth` and `insecureNoAuth`, all optional. `target` is a path within the storage, so this host passes
// Node's `request.url` through unchanged and never composes an absolute
// IRI: `baseIri` tells the engine what the root maps to.
//
// A request may carry `now` and `agent` beside `method` to override the
// handle's clock and agent for one step. That is how a host with a real
// clock and a real token verifier feeds both in; this host sets `now`
// from its own clock only when the caller asked for it, so a test can
// keep the engine's deterministic clock.
//
// `headers` is a list of pairs rather than an object because HTTP allows
// a field name to repeat and the order of repeated fields is
// significant; an object would lose both.
//
// The reader of the response envelope accepts the response record either
// under `response` or spread onto the envelope itself, and the handle
// either as `handle` or as `id`. This is deliberate tolerance while the
// Lean side of the contract lands, not two supported shapes: when
// `docs/lws-solid-conformance.md` fixes one, the other stops being
// produced and this code keeps working unchanged.

import { loadEngine } from '../bin/engine.mjs'
import { readSnapshot, persistIfChanged, storageKeyText, storageModeText, loadFiles, persistFilesIfChanged, readStepBodies } from './persist.mjs'

/** The ops this host needs from the engine. */
export const LWS_OPS = ['lwsOpen', 'lwsStep', 'lwsClose', 'lwsSnapshot', 'lwsFetched', 'lwsDelivered',
  'lwsLoad', 'lwsPersist', 'lwsRead']

/** How long this host waits for the answer to one delivery request before
 *  it reports "no answer" (status 0) to the engine. */
const DELIVERY_TIMEOUT_MS = 10000

/** Random bytes for the engine, base64: `entropy` at open (32 bytes, the
 *  seed of the signing key of a new storage and of the identifiers of one
 *  run) and `random` with each request (16 bytes, the name of a search
 *  results resource when the engine makes one). Pure I/O. */
function entropyBase64 (size = 32) {
  const bytes = new Uint8Array(size)
  globalThis.crypto.getRandomValues(bytes)
  let text = ''
  for (const b of bytes) text += String.fromCharCode(b)
  return btoa(text)
}

/** The most documents one request may make this host fetch before the
 *  engine has answered it. The engine names at most two per issuer (its
 *  metadata, then its key set); this bound only stops a defective module
 *  from looping the host. */
const MAX_FETCHES = 8

/** The most host names one request may make this host resolve. The engine
 *  names at most one (the inbox of a subscription request). */
const MAX_RESOLVES = 4

/** Resolve one host name the engine named. Pure I/O: every address
 *  `dns.lookup` gives, or none when it fails; the engine decides. */
async function resolveHost (host) {
  try {
    const dns = await import('node:dns')
    const found = await dns.promises.lookup(host, { all: true, verbatim: true })
    return found.map((a) => a.address)
  } catch (_error) {
    return []
  }
}

/** The addresses of this machine's network interfaces. Pure I/O. */
async function interfaceAddresses () {
  try {
    const os = await import('node:os')
    return Object.values(os.networkInterfaces()).flat().filter(Boolean).map((i) => i.address)
  } catch (_error) {
    return []
  }
}

/**
 * Fetch one document the engine named, for `lwsFetched`. Pure I/O: the
 * engine decides what the bytes mean. A network failure is reported as
 * status 0, which the engine refuses like any other failed fetch.
 */
async function fetchDocument (url) {
  try {
    const answer = await fetch(url, { redirect: 'error' })
    return { status: answer.status, body: await answer.text() }
  } catch (error) {
    return { status: 0, body: String(error && error.message ? error.message : error) }
  }
}

/** An error raised by the LWS host, as opposed to one the engine
 *  reported. `unknownOp` is set when the loaded WebAssembly module does
 *  not carry the operation at all, which is what a test skips on. */
export class LwsHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'LwsHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the LWS operations.
 *
 * One call is made and its refusal read. A module built before the LWS
 * ops landed answers "unknown op"; anything else -- including an engine
 * complaint about the configuration -- means the op is present.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function lwsOpsAvailable (engine) {
  try {
    const opened = engine.call('lwsOpen', [JSON.stringify({ probe: true })])
    const handle = handleOf(opened)
    if (handle !== null) {
      try { engine.call('lwsClose', [handle]) } catch (_error) { /* probe only */ }
    }
    return { available: true, reason: 'lwsOpen answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry ' +
          'the lws ops (rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'lwsOpen answered with an engine error' }
  }
}

function handleOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') return null
  for (const name of ['handle', 'id']) {
    const value = envelope[name]
    if (typeof value === 'string' && value.length > 0) return value
    if (typeof value === 'number') return String(value)
  }
  return null
}

function responseOf (envelope, bytes) {
  if (envelope === null || typeof envelope !== 'object') {
    throw new LwsHostError('lwsStep answered with no envelope')
  }
  const record = (envelope.response !== null && typeof envelope.response === 'object')
    ? envelope.response
    : envelope
  if (typeof record.status !== 'number') {
    throw new LwsHostError('lwsStep answered with no status in its response record')
  }
  const headers = Array.isArray(record.headers) ? record.headers : []
  const body = bytes instanceof Uint8Array ? bytes : new Uint8Array(0)
  return { status: record.status, headers, body }
}

/** The request content as bytes: a byte array is passed as it is, and a
 *  string (a JavaScript caller's convenience) as its UTF-8 bytes. */
function contentBytes (request) {
  if (request.body instanceof Uint8Array) return request.body
  if (typeof request.body === 'string') return new TextEncoder().encode(request.body)
  return new Uint8Array(0)
}

/**
 * Open one LWS storage on the engine and return the handle plus the two
 * calls a host makes against it.
 *
 * The config members are the ABI's own: `baseIri`, `now`, `owner`, `pageSize`,
 * `agent`. Nothing else is sent.
 *
 * @param {object} options
 * @param {string} [options.baseIri] the absolute IRI the storage root maps to
 * @param {number} [options.now] the engine clock, seconds since the epoch
 * @param {string} [options.owner] the WebID the storage advertises
 * @param {string} [options.agent] the WebID of the requesting agent
 * @param {number} [options.pageSize] the container pagination threshold and page size (default 100; 0 turns pagination off)
 * @param {boolean} [options.paginateAlways] present every container listing as paginated (default false)
 * @param {boolean|string} [options.moves] which resources move: true or "all", "data", false or "off" (default all)
 * @param {boolean} [options.linksetPut] does a linkset accept PUT (default true)
 * @param {boolean} [options.realClock] stamp each request with this host's clock
 * @param {string|null} [options.storageKey] the storage key text (64 hex digits or base64url);
 *   default the environment variable FACTOIDAL_LWS_KEY; `null` reads no key
 * @param {string} [options.storage] where DIR keeps the storage: "snapshot" (default, one
 *   file) or "files" (one file per body and a journal, issue 918); passed unread
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{step: Function, close: Function, handle: string, engine: object}>}
 */
export async function openLwsStorage (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const config = {}
  if (typeof options.baseIri === 'string') config.baseIri = options.baseIri
  if (typeof options.now === 'number') config.now = options.now
  if (typeof options.owner === 'string') config.owner = options.owner
  if (typeof options.agent === 'string') config.agent = options.agent
  // The pagination threshold and page size of container listings; the
  // engine decides what it means (L4Factoidal/LWS/Pagination.lean).
  if (typeof options.pageSize === 'number') config.pageSize = options.pageSize
  // Authorization (L4Factoidal/LWS/Authorization.lean). `auth` is passed
  // through unread; `insecureNoAuth` is the explicit development mode.
  // With neither, the engine enforces authorization with no trusted
  // issuer.
  if (options.auth !== undefined && options.auth !== null) config.auth = options.auth
  if (options.insecureNoAuth === true) config.insecureNoAuth = true
  if (typeof options.rootAcl === 'string') config.rootAcl = options.rootAcl
  // Notifications are on unless the caller turns them off; the engine
  // decides everything else about them.
  if (options.notifications === false) config.notifications = false
  // The Type Index and Type Search services are on unless the caller turns
  // them off (L4Factoidal/LWS/Search.lean).
  if (options.typeIndex === false) config.typeIndex = false
  // Moves (a change of the up link, L4Factoidal/LWS/Move.lean) are on
  // unless the caller turns them off.
  if (options.moves === false) config.moves = false
  // `moves` may also be "all", "data" or "off", passed unread; the engine
  // decides what each means and refuses another value (Wasm/Ops/Lws.lean).
  if (typeof options.moves === 'string') config.moves = options.moves
  // A linkset resource accepts PUT unless the caller turns it off
  // (L4Factoidal/LWS/Operations.lean, linksetStep).
  if (options.linksetPut === false) config.linksetPut = false
  // Every container listing paginated, also one that fits on one page
  // (L4Factoidal/LWS/Pagination.lean, paginatedWith). Off unless turned on.
  if (options.paginateAlways === true) config.paginateAlways = true
  // Access requests and grants are on unless the caller turns them off
  // (L4Factoidal/LWS/AccessGrants.lean).
  if (options.accessGrants === false) config.accessGrants = false
  // ANTICIPATORY AND UNSTABLE (https://github.com/danbri/factoidal/issues/922):
  // a QUERY answer of the type search names a results resource with
  // Content-Location. Off unless the caller turns it on
  // (L4Factoidal/LWS/SearchResults.lean decides everything about it).
  if (options.searchResults === true) config.searchResults = true
  if (typeof options.searchResultsTtl === 'number') config.searchResultsTtl = options.searchResultsTtl
  if (typeof options.searchResultsMax === 'number') config.searchResultsMax = options.searchResultsMax
  // Merkle hashes (https://github.com/danbri/factoidal/issues/919): off
  // unless the caller turns them on (L4Factoidal/LWS/MerkleHttp.lean decides
  // every field and member they add).
  if (options.merkle === true) config.merkle = true
  // Webhook delivery rate (issue 915), the redirect table bound (issue 914)
  // and the storage controller's inbox (issue 920): passed unread; the
  // engine checks and decides.
  if (typeof options.deliveryLimit === 'number') config.deliveryLimit = options.deliveryLimit
  if (typeof options.deliveryWindow === 'number') config.deliveryWindow = options.deliveryWindow
  if (typeof options.redirectsMax === 'number') config.redirectsMax = options.redirectsMax
  if (typeof options.controllerInbox === 'string') config.controllerInbox = options.controllerInbox
  // What this host bound: data for the engine's inbox check (issue 915).
  if (options.listen !== undefined && options.listen !== null) config.listen = options.listen
  config.entropy = entropyBase64()
  // Encryption at rest (issue 921): the key text from `storageKey` or the
  // environment variable FACTOIDAL_LWS_KEY, passed unread. The engine checks
  // it, refuses a file that does not match it, and seals every snapshot.
  const storageKey = storageKeyText(options.storageKey)
  if (storageKey !== undefined) config.storageKey = storageKey
  // Where the storage is kept (https://github.com/danbri/factoidal/issues/918):
  // `storage` is passed unread; the engine refuses a value it does not know.
  // With "files" the engine names the files to read (`load`) and gives the
  // plan of every write (`lwsPersist`), and this host reads no snapshot.
  // With a DIR and no `storage` option, the environment variable
  // FACTOIDAL_LWS_STORAGE is the value; without a DIR there is nothing to
  // keep, and only an explicit option is passed.
  const dir = typeof options.dir === 'string' ? options.dir : null
  const storage = dir !== null ? storageModeText(options.storage) : options.storage
  if (typeof storage === 'string') config.storage = storage
  // `dir` names the storage directory. The snapshot found there, if any,
  // is the storage to continue from; the engine checks it.
  if (dir !== null && storage !== 'files') {
    const snapshot = readSnapshot(dir)
    if (snapshot !== null) config.snapshot = snapshot
  }
  let opened
  try {
    opened = engine.call('lwsOpen', [JSON.stringify(config)])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new LwsHostError(
        'the loaded l4factoidal WebAssembly module does not carry lwsOpen',
        { unknownOp: true })
    }
    throw error
  }
  const handle = handleOf(opened)
  if (handle === null) {
    throw new LwsHostError('lwsOpen answered with no handle')
  }
  // A storage kept in files: read the files the engine names until it is
  // ready, and perform the plan of the start. Without a DIR, there are no
  // files: the engine is told none is present.
  const filesMode = opened !== null && typeof opened === 'object' &&
    opened.load !== undefined && opened.load !== null
  if (filesMode) {
    if (dir === null) throw new LwsHostError('a storage kept in files needs a storage directory (dir)')
    loadFiles(engine, handle, opened, dir)
  }
  /** After a call whose envelope may say `changed`: write what the engine
   *  gives (the snapshot, or the plan of a storage kept in files). */
  const persist = (envelope) => {
    if (dir === null) return
    if (filesMode) persistFilesIfChanged(engine, handle, envelope, dir)
    else persistIfChanged(engine, 'lwsSnapshot', handle, envelope, dir)
  }

  // Deliveries in flight, so a caller (a test, a shutdown) can wait.
  const inFlight = new Set()
  let closed = false
  // The one timer that calls `lwsFlush` when the engine named a `wake`.
  let flushTimer = null
  let flushAt = Infinity
  const clockNow = () => (options.realClock === true ? { now: Math.floor(Date.now() / 1000) } : {})

  /** Make one delivery request the engine named, report the status, and
   *  follow the engine's answer. */
  function deliver (delivery) {
    const job = (async () => {
      let status = 0
      try {
        const answer = await fetch(delivery.url, {
          method: 'POST',
          headers: Array.isArray(delivery.headers) ? delivery.headers : [],
          body: delivery.body,
          redirect: 'manual',
          signal: AbortSignal.timeout(DELIVERY_TIMEOUT_MS)
        })
        status = answer.status
        await answer.arrayBuffer()
      } catch (_error) {
        status = 0
      }
      if (closed) return
      const told = engine.call('lwsDelivered', [handle, JSON.stringify({
        id: delivery.id, status, ...clockNow()
      })])
      persist(told)
      const retry = told !== null && typeof told === 'object' ? told.retry : null
      if (retry !== undefined && retry !== null && typeof retry.after === 'number') {
        await new Promise((resolve) => {
          const timer = setTimeout(resolve, retry.after * 1000)
          if (timer && typeof timer.unref === 'function') timer.unref()
        })
        if (!closed) deliver(retry.delivery)
      }
    })()
    inFlight.add(job)
    // A failure here is a failure of this host or of the engine call, not a
    // protocol answer; it is reported and the delivery is dropped.
    job.catch((error) => { console.error(`lws-serve: delivery: ${error && error.message ? error.message : error}`) })
      .finally(() => inFlight.delete(job))
  }

  /** Call `lwsFlush` after `seconds`, unless an earlier call is due. */
  function scheduleFlush (seconds) {
    if (closed || typeof seconds !== 'number') return
    const at = Date.now() + seconds * 1000
    if (flushTimer !== null && flushAt <= at) return
    if (flushTimer !== null) clearTimeout(flushTimer)
    flushAt = at
    flushTimer = setTimeout(() => {
      flushTimer = null
      flushAt = Infinity
      if (closed) return
      try {
        const told = engine.call('lwsFlush', [handle, JSON.stringify(clockNow())])
        persist(told)
        if (told !== null && typeof told === 'object') {
          if (Array.isArray(told.deliveries)) for (const delivery of told.deliveries) deliver(delivery)
          if (typeof told.wake === 'number') scheduleFlush(told.wake)
        }
      } catch (error) {
        console.error(`lws-serve: flush: ${error && error.message ? error.message : error}`)
      }
    }, seconds * 1000)
    if (flushTimer && typeof flushTimer.unref === 'function') flushTimer.unref()
  }

  return {
    engine,
    handle,
    /**
     * One protocol step.
     * @param {{method: string, target: string,
     *          headers: Array<[string, string]>, body: Uint8Array|string}} request
     * @returns {{status: number, headers: Array<[string, string]>, body: Uint8Array}}
     */
    async step (request) {
      const content = contentBytes(request)
      const { body: _body, ...fields } = request
      // Random bytes with every request; the engine uses them only to name
      // a search results resource (issue 922), and only when that is on.
      const stamped = { ...fields, random: entropyBase64(16) }
      const record = options.realClock === true
        ? { ...stamped, now: Math.floor(Date.now() / 1000) }
        : stamped
      // The engine may ask for the addresses of a host name first
      // (`resolve`); this host resolves it and steps the request again.
      let resolves = 0
      // A storage kept in files (https://github.com/danbri/factoidal/issues/918,
      // stage 2) may answer `read: [NAME, ...]` first: the body files the step
      // needs. This host reads exactly those files, passes them to `lwsRead`
      // (the engine checks them), and steps the same request again.
      const callStep = () => {
        let got = engine.callBlobIO('lwsStep', [handle, JSON.stringify(record)], content)
        let reads = 0
        while (got.envelope !== null && typeof got.envelope === 'object' && Array.isArray(got.envelope.read)) {
          reads += 1
          if (reads > 2 || dir === null) {
            throw new LwsHostError('the engine asked for body files this host cannot read')
          }
          readStepBodies(engine, handle, got.envelope.read, dir)
          got = engine.callBlobIO('lwsStep', [handle, JSON.stringify(record)], content)
        }
        return got
      }
      let answered = callStep()
      let envelope = answered.envelope
      while (envelope !== null && typeof envelope === 'object' &&
             envelope.resolve !== undefined && envelope.resolve !== null) {
        resolves += 1
        if (resolves > MAX_RESOLVES) {
          throw new LwsHostError('the engine asked for more host names than one request may resolve')
        }
        const host = String(envelope.resolve.host)
        const addresses = await resolveHost(host)
        record.resolved = [...(Array.isArray(record.resolved) ? record.resolved : []), { host, addresses }]
        answered = callStep()
        envelope = answered.envelope
      }
      // The engine may answer "fetch this document first" (an issuer's
      // metadata or key set). The host fetches exactly what it is told,
      // hands the bytes back, and steps the request again.
      let fetches = 0
      while (envelope !== null && typeof envelope === 'object' &&
             envelope.fetch !== undefined && envelope.fetch !== null) {
        let wanted = envelope.fetch
        while (wanted !== undefined && wanted !== null) {
          fetches += 1
          if (fetches > MAX_FETCHES) {
            throw new LwsHostError('the engine asked for more documents than one request may fetch')
          }
          const got = await fetchDocument(wanted.url)
          const told = engine.call('lwsFetched', [handle, JSON.stringify({
            issuer: wanted.issuer, url: wanted.url, status: got.status, body: got.body,
            ...(typeof record.now === 'number' ? { now: record.now } : {})
          })])
          wanted = told !== null && typeof told === 'object' ? told.fetch : null
        }
        answered = callStep()
        envelope = answered.envelope
      }
      const answer = responseOf(envelope, answered.bytes)
      persist(envelope)
      if (Array.isArray(envelope.deliveries)) {
        // After this step's answer is ready; the engine's state already
        // records them as pending.
        for (const delivery of envelope.deliveries) setTimeout(() => deliver(delivery), 0)
      }
      if (typeof envelope.wake === 'number') scheduleFlush(envelope.wake)
      return answer
    },
    /** Resolves when no delivery request is in flight. */
    async settled () {
      await new Promise((resolve) => setTimeout(resolve, 0))
      while (inFlight.size > 0) await Promise.allSettled([...inFlight])
    },
    close () {
      closed = true
      if (flushTimer !== null) clearTimeout(flushTimer)
      try { engine.call('lwsClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** Read a Node request body as its bytes. */
function readBody (request) {
  return new Promise((resolve, reject) => {
    const chunks = []
    request.on('data', (chunk) => chunks.push(chunk))
    request.on('error', reject)
    request.on('end', () => resolve(new Uint8Array(Buffer.concat(chunks))))
  })
}

/** Node's flat `rawHeaders` array as the pairs the contract wants. */
function headerPairs (raw) {
  const pairs = []
  for (let index = 0; index + 1 < raw.length; index += 2) {
    pairs.push([raw[index], raw[index + 1]])
  }
  return pairs
}

/**
 * A Node `http.Server` that answers every request through `lwsStep`.
 *
 * The server is returned unlistened: the caller chooses the port, which
 * is what lets a test take an ephemeral one. The storage handle is
 * opened on demand rather than here, because with an ephemeral port the
 * origin `baseIri` maps the storage root to is not known until the
 * socket is bound.
 *
 * @param {object} options as `openLwsStorage`, plus `onError`
 * @returns {Promise<{server: import('node:http').Server,
 *                    storage: Function, close: Function,
 *                    setBaseIri: Function}>}
 */
export async function createLwsServer (options = {}) {
  const http = await import('node:http')
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`lws-serve: ${error.message}`) }

  let settings = { ...options }
  let opening = null
  let opened = null

  /** The storage handle, opened once. */
  function storage () {
    if (opening === null) {
      opening = openLwsStorage(settings).then((value) => { opened = value; return value })
    }
    return opening
  }

  const server = http.createServer(async (request, response) => {
    let record
    try {
      record = {
        method: request.method,
        target: request.url,
        headers: headerPairs(request.rawHeaders),
        body: await readBody(request)
      }
    } catch (error) {
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end('lws-serve: could not read the request body\n')
      return
    }
    let answer
    try {
      answer = await (await storage()).step(record)
    } catch (error) {
      // A failure of this host or of the engine, not a protocol answer.
      // The engine's own words are kept; nothing is invented.
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end(`lws-serve: ${error.message}\n`)
      return
    }
    writeHeaders(response, answer.headers)
    response.statusCode = answer.status
    response.end(answer.body)
  })

  return {
    server,
    storage,
    /** Set the storage root's absolute IRI, before the first request. */
    setBaseIri (value) {
      if (opening !== null) {
        throw new LwsHostError('the storage is already open; set baseIri first')
      }
      settings = { ...settings, baseIri: value }
    },
    /** Pass what the socket bound (address, port, interface addresses),
     *  before the first request. Data for the engine's inbox check. */
    setListen (value) {
      if (opening !== null) {
        throw new LwsHostError('the storage is already open; set listen first')
      }
      settings = { ...settings, listen: value }
    },
    close () {
      return new Promise((resolve) => {
        server.close(() => {
          if (opened !== null) opened.close()
          resolve()
        })
      })
    }
  }
}

/** Write one response record's header pairs, keeping repeats. */
function writeHeaders (response, pairs) {
  for (const pair of pairs) {
    if (!Array.isArray(pair) || pair.length < 2) continue
    const existing = response.getHeader(pair[0])
    if (existing === undefined) {
      response.setHeader(pair[0], String(pair[1]))
    } else if (Array.isArray(existing)) {
      response.setHeader(pair[0], existing.concat([String(pair[1])]))
    } else {
      response.setHeader(pair[0], [String(existing), String(pair[1])])
    }
  }
}

/**
 * Start a server and resolve once it is listening and the storage is
 * open. The storage is opened here rather than on the first request so
 * that a module without the LWS ops is reported by the command that
 * started the server, not by a later request.
 *
 * @param {object} options as `createLwsServer`, plus `port` and `host`
 * @returns {Promise<{server: object, storage: Function, port: number,
 *                    origin: string, close: Function}>}
 */
export async function listen (options = {}) {
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const created = await createLwsServer(options)
  await new Promise((resolve, reject) => {
    created.server.once('error', reject)
    created.server.listen(port, host, resolve)
  })
  const bound = created.server.address()
  const origin = `http://${host}:${bound.port}`
  if (typeof options.baseIri !== 'string') created.setBaseIri(`${origin}/`)
  created.setListen({ address: bound.address, port: bound.port, addresses: await interfaceAddresses() })
  try {
    await created.storage()
  } catch (error) {
    await new Promise((resolve) => created.server.close(resolve))
    throw error
  }
  return { ...created, port: bound.port, origin }
}
