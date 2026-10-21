// A Node HTTP host for the Solid Protocol v0.11.0 server conformance class.
// https://github.com/danbri/factoidal/issues/659
// Design record: docs/designissues/2026-09-06-lws-and-solid-protocols.md
// Specification: https://solidproject.org/TR/protocol
//
// WHAT THIS FILE IS ALLOWED TO DO
// Accept a socket, turn one HTTP request into the JSON request record,
// call the engine's `solidStep` on a handle, and write the JSON response
// record back. Nothing else.
//
// It decides no status code, builds no `Link` header, writes no
// containment triple, reads no ACL and answers no OPTIONS. Storage
// discovery, containment, slash semantics, the auxiliary lifecycle, N3
// Patch, Web Access Control, CORS and the LDN inbox are all in
// `formal/lean4/L4Factoidal/Solid/Server/` (iron rule 7 of CLAUDE.md).
// The CORS PREFLIGHT is not an exception: an OPTIONS request is passed
// to `solidStep` like every other request and the engine's headers are
// written back unread. The only status this file writes is 500, for a
// failure of the host itself.
//
// THE WASM CONTRACT
// Fixed in docs/lws-solid-conformance.md, section "wasm ABI".
//   solidOpen  [configJson]            -> { ok, handle, root, storage }
//   solidStep  [handle, requestJson]   -> { ok, response }
//   solidClose [handle]                -> { ok }
//   solidFetched [handle, documentJson] -> { ok, fetch? | installed? | refused? }
//
// Solid-OIDC (issue 899): with `auth` in the configuration the engine
// verifies the DPoP-bound access token itself
// (formal/lean4/L4Factoidal/Solid/Server/Oidc.lean). When it needs a
// document it does not hold -- an issuer's OpenID configuration, its JWK
// Set, or a WebID profile -- `solidStep` answers `{ fetch: {kind, key,
// url} }`. This host fetches exactly that URL, hands status and body to
// `solidFetched` unread, follows any `fetch` that answers, and steps the
// request again. It chooses no URL and reads no document.
//
//   request  { method, target, headers: [[name, value]], body }
//   response { status, headers: [[name, value]], body }
//
// The config members are `baseIri` (the absolute IRI the storage root
// maps to), `now` (the engine clock in seconds, which advances by one
// second per mutation so a write sequence has increasing Last-Modified
// values with no real clock), `owner` and `agent`. All are optional.
//
// `target` is a path within the storage, so Node's `request.url` is
// passed through unchanged and this host composes no IRI. With an
// ephemeral port the origin is not known until the socket is bound, so
// the storage handle is opened after binding rather than before.
//
// `agent` is the WebID of the requesting agent. It stands only when the
// configuration has no `auth` (or has `insecureNoAuth`); with `auth` the
// engine decides the WebID from the credential.
//
// This file shares no code with `../client/index.mjs` beyond the engine
// loader, by the design record's rule that the two conformance classes
// stay distinct.

import { loadEngine } from '../../bin/engine.mjs'
import { readSnapshot, persistIfChanged, storageKeyText } from '../../lws/persist.mjs'

/** The ops this host needs from the engine. */
export const SOLID_SERVER_OPS = ['solidOpen', 'solidStep', 'solidClose', 'solidSnapshot',
  'solidFetched']

/** The most documents one request may make this host fetch. The engine
 *  names at most three per request (issuer metadata, key set, profile);
 *  this bound only stops a defective module from looping the host. */
const MAX_FETCHES = 8

/** Fetch one document the engine named. Pure I/O; a network failure is
 *  status 0, which the engine refuses like any failed fetch. */
async function fetchDocument (url) {
  try {
    const answer = await fetch(url, {
      redirect: 'error',
      headers: { accept: 'text/turtle, application/json;q=0.9, */*;q=0.1' }
    })
    return { status: answer.status, body: await answer.text() }
  } catch (error) {
    return { status: 0, body: String(error && error.message ? error.message : error) }
  }
}

/** An error raised by the Solid server host. `unknownOp` is set when the
 *  loaded WebAssembly module does not carry the operation at all, which
 *  is what a test skips on. */
export class SolidServerHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'SolidServerHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the Solid server operations.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function solidServerOpsAvailable (engine) {
  try {
    const opened = engine.call('solidOpen', [JSON.stringify({ probe: true })])
    const handle = handleOf(opened)
    if (handle !== null) {
      try { engine.call('solidClose', [handle]) } catch (_error) { /* probe only */ }
    }
    return { available: true, reason: 'solidOpen answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry ' +
          'the solid server ops (rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'solidOpen answered with an engine error' }
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
    throw new SolidServerHostError('solidStep answered with no envelope')
  }
  const record = (envelope.response !== null && typeof envelope.response === 'object')
    ? envelope.response
    : envelope
  if (typeof record.status !== 'number') {
    throw new SolidServerHostError(
      'solidStep answered with no status in its response record')
  }
  return {
    status: record.status,
    headers: Array.isArray(record.headers) ? record.headers : [],
    body: bytes instanceof Uint8Array ? bytes : new Uint8Array(0)
  }
}

/** The request content as bytes: a byte array is passed as it is, and a
 *  string (a JavaScript caller's convenience) as its UTF-8 bytes. Bodies
 *  are bytes end to end (https://github.com/danbri/factoidal/issues/889). */
function contentBytes (request) {
  if (request.body instanceof Uint8Array) return request.body
  if (typeof request.body === 'string') return new TextEncoder().encode(request.body)
  return new Uint8Array(0)
}

/**
 * Open one Solid storage on the engine.
 *
 * @param {object} options
 * @param {string} [options.baseIri] the absolute IRI the storage root maps to
 * @param {number} [options.now] the engine clock, seconds since the epoch
 * @param {string} [options.owner] the WebID the storage advertises
 * @param {string} [options.agent] the WebID of the requesting agent
 * @param {boolean} [options.realClock] stamp each request with this host's clock
 * @param {string|null} [options.storageKey] the storage key text (64 hex digits or base64url);
 *   default the environment variable FACTOIDAL_LWS_KEY; `null` reads no key
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{step: Function, close: Function, handle: string,
 *                    engine: object}>}
 */
export async function openSolidStorage (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const config = {}
  if (typeof options.baseIri === 'string') config.baseIri = options.baseIri
  if (typeof options.now === 'number') config.now = options.now
  if (typeof options.owner === 'string') config.owner = options.owner
  if (typeof options.agent === 'string') config.agent = options.agent
  // Solid-OIDC: `auth` is passed through unread; `insecureNoAuth` is the
  // explicit development mode.
  if (options.auth !== undefined && options.auth !== null) config.auth = options.auth
  if (options.insecureNoAuth === true) config.insecureNoAuth = true
  if (typeof options.enforceWac === 'boolean') config.enforceWac = options.enforceWac
  if (typeof options.rootAcl === 'string') config.rootAcl = options.rootAcl
  // Encryption at rest (issue 921), as the LWS host: the key text from
  // `storageKey` or FACTOIDAL_LWS_KEY, passed unread; the engine decides.
  const storageKey = storageKeyText(options.storageKey)
  if (storageKey !== undefined) config.storageKey = storageKey
  // `dir` names the storage directory. The snapshot found there, if any,
  // is the storage to continue from; the engine checks it.
  const dir = typeof options.dir === 'string' ? options.dir : null
  if (dir !== null) {
    const snapshot = readSnapshot(dir)
    if (snapshot !== null) config.snapshot = snapshot
  }
  let opened
  try {
    opened = engine.call('solidOpen', [JSON.stringify(config)])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new SolidServerHostError(
        'the loaded l4factoidal WebAssembly module does not carry solidOpen',
        { unknownOp: true })
    }
    throw error
  }
  const handle = handleOf(opened)
  if (handle === null) {
    throw new SolidServerHostError('solidOpen answered with no handle')
  }
  return {
    engine,
    handle,
    storageIri: typeof opened.storage === 'string' ? opened.storage : null,
    /**
     * One protocol step.
     * @param {{method: string, target: string,
     *          headers: Array<[string, string]>, body: Uint8Array|string}} request
     * @returns {{status: number, headers: Array<[string, string]>, body: Uint8Array}}
     */
    async step (request) {
      const content = contentBytes(request)
      const { body: _body, ...fields } = request
      const record = options.realClock === true
        ? { ...fields, now: Math.floor(Date.now() / 1000) }
        : fields
      // The byte-region entry: request content in, response content out.
      const callStep = () =>
        engine.callBlobIO('solidStep', [handle, JSON.stringify(record)], content)
      let { envelope, bytes } = callStep()
      let fetches = 0
      while (envelope !== null && typeof envelope === 'object' &&
             envelope.fetch !== undefined && envelope.fetch !== null) {
        let wanted = envelope.fetch
        while (wanted !== undefined && wanted !== null) {
          fetches += 1
          if (fetches > MAX_FETCHES) {
            throw new SolidServerHostError('the engine asked for more documents than one request may fetch')
          }
          const got = await fetchDocument(wanted.url)
          const told = engine.call('solidFetched', [handle, JSON.stringify({
            kind: wanted.kind, key: wanted.key, url: wanted.url, status: got.status, body: got.body,
            ...(typeof record.now === 'number' ? { now: record.now } : {})
          })])
          wanted = told !== null && typeof told === 'object' ? told.fetch : null
        }
        ({ envelope, bytes } = callStep())
      }
      const answer = responseOf(envelope, bytes)
      if (dir !== null) persistIfChanged(engine, 'solidSnapshot', handle, envelope, dir)
      return answer
    },
    close () {
      try { engine.call('solidClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

function readBody (request) {
  return new Promise((resolve, reject) => {
    const chunks = []
    request.on('data', (chunk) => chunks.push(chunk))
    request.on('error', reject)
    request.on('end', () => resolve(new Uint8Array(Buffer.concat(chunks))))
  })
}

function headerPairs (raw) {
  const pairs = []
  for (let index = 0; index + 1 < raw.length; index += 2) {
    pairs.push([raw[index], raw[index + 1]])
  }
  return pairs
}

/**
 * A Node `http.Server` that answers every request through `solidStep`.
 *
 * Returned unlistened, so a test can take an ephemeral port. The storage
 * handle is opened on demand, because `baseIri` is not known until the
 * socket is bound.
 *
 * @param {object} options as `openSolidStorage`, plus `onError`
 * @returns {Promise<{server: object, storage: Function, close: Function,
 *                    setBaseIri: Function}>}
 */
export async function createSolidServer (options = {}) {
  const http = await import('node:http')
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`solid-serve: ${error.message}`) }

  let settings = { ...options }
  let opening = null
  let opened = null

  function storage () {
    if (opening === null) {
      opening = openSolidStorage(settings).then((value) => { opened = value; return value })
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
      response.end('solid-serve: could not read the request body\n')
      return
    }
    let answer
    try {
      answer = await (await storage()).step(record)
    } catch (error) {
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end(`solid-serve: ${error.message}\n`)
      return
    }
    writeHeaders(response, answer.headers)
    response.statusCode = answer.status
    response.end(answer.body)
  })

  return {
    server,
    storage,
    setBaseIri (value) {
      if (opening !== null) {
        throw new SolidServerHostError('the storage is already open; set baseIri first')
      }
      settings = { ...settings, baseIri: value }
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
 * Start a Solid server and resolve once it is listening and the storage
 * is open, so that a module without the Solid ops is reported by the
 * command that started the server rather than by a later request.
 *
 * @param {object} options as `createSolidServer`, plus `port` and `host`
 * @returns {Promise<{server: object, storage: Function, port: number,
 *                    origin: string, close: Function}>}
 */
export async function listen (options = {}) {
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const created = await createSolidServer(options)
  await new Promise((resolve, reject) => {
    created.server.once('error', reject)
    created.server.listen(port, host, resolve)
  })
  const bound = created.server.address()
  const origin = `http://${host}:${bound.port}`
  if (typeof options.baseIri !== 'string') created.setBaseIri(`${origin}/`)
  try {
    await created.storage()
  } catch (error) {
    await new Promise((resolve) => created.server.close(resolve))
    throw error
  }
  return { ...created, port: bound.port, origin }
}
