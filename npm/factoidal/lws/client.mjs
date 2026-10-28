// A `fetch` host for the Linked Web Storage 1.0 client.
// https://github.com/danbri/factoidal/issues/917
// Design record: docs/designissues/2026-10-22-lws-client.md
// Drafts: https://w3c.github.io/lws-protocol/lws10-core/ (and lws10-index,
// lws10-notifications-webhook)
//
// WHAT THIS FILE IS ALLOWED TO DO
// Call `lwsClientStart` with the caller's operation, then loop: when the
// engine's action is `fetch`, send exactly that request with the `fetch`
// it was given and pass the answer to `lwsClientStep`; when it is `done` or
// `fail`, return or throw. It is a socket and nothing else.
//
// Every decision is in formal/lean4/L4Factoidal/LWS/Client/ (iron rule 7
// of CLAUDE.md, anti-pattern 36): which request comes next, every header
// field, every URL, every media type, the authorization flow and its
// discovery checks, preconditions, retries, paging, and whether a
// notification's signature verifies. This file reads no header, composes no
// URL and chooses no media type. A reviewer who finds a header name, a
// status code, a media type or a link relation here has found a rule
// violation.
//
// THE WASM CONTRACT (docs/lws-solid-conformance.md, section "wasm ABI")
//   lwsClientStart [opJson, sessionJson] -> { ok, state, action }
//   lwsClientStep  [stateJson, eventJson] -> { ok, state, action }
//
//   action  { fetch: { method, url, headers: [[name, value]], bodyBase64? } }
//         | { done: RESULT, session } | { fail: { code, ... }, session }
//   event   { status, headers: [[name, value]], bodyBase64 } | { error }
//
// `state` is passed back unread. `session` (access tokens, the subject
// token) is kept here and given to the next operation's start, unread.
//
// `fetch` is any function with the WHATWG fetch signature: Node's, a
// browser's, or one that carries each request as a message over another
// transport (XMPP, a worker port). The client needs no global fetch.

import { loadEngine } from '../bin/engine.mjs'
import { FactoidalError } from '../lib/errors.mjs'

/** The ops this host needs from the engine. */
export const LWS_CLIENT_OPS = ['lwsClientStart', 'lwsClientStep', 'lwsClientNewKey']

/** The operation kinds of the ABI. Listed so a caller can be checked
 *  against the contract; this host attaches no meaning to any of them. */
export const LWS_CLIENT_KINDS = [
  'discover', 'describe', 'read', 'readPage', 'head', 'create', 'update', 'patch', 'delete',
  'findLinkset', 'readLinkset', 'updateLinkset', 'putLinkset', 'move', 'list', 'typeIndex',
  'search', 'queryFormats', 'subscribe', 'getSubscription', 'unsubscribe', 'requestAccess',
  'grantAccess', 'getAccess', 'revokeAccess', 'verifyNotification'
]

/** The error an operation ends with. `reason` is the engine's code
 *  (`discoveryValidation`, `preconditionFailed`, ...); `detail` is the
 *  engine's whole `fail` document. */
export class LwsClientError extends FactoidalError {
  constructor (fail, extra = {}) {
    const reason = fail && typeof fail.code === 'string' ? fail.code : 'unknown'
    super(`lws client: ${reason}`, { code: 'lws.client' })
    this.name = 'LwsClientError'
    this.reason = reason
    this.detail = fail
    // The engine's name for the failure in the lws-driver/1 adapter
    // protocol ({ kind, message, ... }), as the engine wrote it.
    this.report = fail && typeof fail.report === 'object' ? fail.report : undefined
    this.unknownOp = extra.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/** Bytes as base64 (RFC 4648 section 4): the transport encoding of the
 *  string ABI, not a reading of the bytes. */
function base64OfBytes (bytes) {
  if (typeof Buffer !== 'undefined') {
    return Buffer.from(bytes.buffer, bytes.byteOffset, bytes.byteLength).toString('base64')
  }
  let text = ''
  for (let index = 0; index < bytes.length; index += 1) text += String.fromCharCode(bytes[index])
  return btoa(text)
}

function bytesOfBase64 (text) {
  if (typeof Buffer !== 'undefined') return new Uint8Array(Buffer.from(text, 'base64'))
  const raw = atob(text)
  const out = new Uint8Array(raw.length)
  for (let index = 0; index < raw.length; index += 1) out[index] = raw.charCodeAt(index)
  return out
}

/** A caller's body (string, Uint8Array, ArrayBuffer) as bytes. */
function bytesOf (body) {
  if (body === undefined || body === null) return null
  if (typeof body === 'string') return new TextEncoder().encode(body)
  if (body instanceof Uint8Array) return body
  if (body instanceof ArrayBuffer) return new Uint8Array(body)
  throw new TypeError('a body is a string, a Uint8Array or an ArrayBuffer')
}

/** An operation document: the caller's members, with a body carried as
 *  base64. */
function opDocument (op) {
  const doc = { ...op }
  if (doc.body !== undefined) {
    const bytes = bytesOf(doc.body)
    delete doc.body
    if (bytes !== null) doc.bodyBase64 = base64OfBytes(bytes)
  }
  return doc
}

/**
 * Whether the loaded engine carries the client operations.
 *
 * @param {object} engine the handle from `loadEngine()`
 * @returns {Promise<{available: boolean, reason: string}>}
 */
export async function lwsClientOpsAvailable (engine) {
  try {
    engine.call('lwsClientStart', [JSON.stringify({ kind: 'head', url: 'http://localhost/' }), ''])
    return { available: true, reason: 'lwsClientStart answered' }
  } catch (error) {
    if (isUnknownOp(error)) {
      return {
        available: false,
        reason: 'the loaded l4factoidal WebAssembly module does not carry the LWS client ops ' +
          '(rebuild formal/lean4/Wasm)'
      }
    }
    return { available: true, reason: 'lwsClientStart answered with an engine error' }
  }
}

/**
 * An LWS client bound to one engine and one `fetch`.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @param {Function} [options.fetch] the fetch to use (default `globalThis.fetch`)
 * @param {string} [options.subjectToken] the authentication credential to
 *   exchange for access tokens (RFC 8693 subject_token)
 * @param {string} [options.subjectTokenType] its token type URI
 * @param {object} [options.selfIssued] `{ subject, keyId, jwk }`: a P-256 or
 *   Ed25519 key to sign self-issued credentials with, instead of a subject
 *   token (`createDidKey` makes one)
 * @param {string} [options.idToken] an OpenID Connect ID Token to exchange
 * @param {object} [options.bearer] `{ token, realm? }`: an access token the
 *   caller already has; with a realm it is sent only under it
 * @param {boolean} [options.legacyChallenge] follow the 401 challenge
 *   `Bearer as_uri="…", realm="…"` of the drafts before 2026-10-19 (default
 *   false: it skips two of the discovery checks of lws10-core)
 * @param {boolean} [options.requireHttps] send no request to a URL whose
 *   scheme is not https, in any phase; such an operation fails with code
 *   `insecureTransport` (default false; the engine decides)
 * @param {object} [options.session] a session from an earlier client
 * @param {number} [options.maxSteps] the loop cap of one operation
 * @returns {Promise<object>} the client
 */
export async function createLwsClient (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const wire = typeof options.fetch === 'function' ? options.fetch : globalThis.fetch
  if (typeof wire !== 'function') throw new TypeError('no fetch is available in this runtime')
  const maxSteps = typeof options.maxSteps === 'number' ? options.maxSteps : 1024
  let session = options.session !== undefined && options.session !== null
    ? { ...options.session }
    : {}
  if (typeof options.subjectToken === 'string') session.subjectToken = options.subjectToken
  if (typeof options.subjectTokenType === 'string') session.subjectTokenType = options.subjectTokenType
  // `{ subject, keyId, jwk }`: a P-256 key the engine signs self-issued
  // credentials with (lws10-authn-ssi-cid), passed through unread.
  if (options.selfIssued !== undefined) session.selfIssued = options.selfIssued
  // Read by the engine's session reader (`Machine.sessionOfJson`), unread here.
  if (options.idToken !== undefined) session.idToken = options.idToken
  if (options.bearer !== undefined) session.bearer = options.bearer
  // Follow the `Bearer as_uri, realm` challenge of the drafts before
  // 2026-10-19 (`Machine.on401`); the engine decides, off by default.
  if (options.legacyChallenge === true) session.legacyChallenge = true
  // Refuse every request to a URL that is not https (`Machine.enforce`).
  if (options.requireHttps === true) session.requireHttps = true

  function call (op, args) {
    try {
      return engine.call(op, args)
    } catch (error) {
      if (isUnknownOp(error)) {
        throw new LwsClientError({ code: 'unknownOp', op }, { unknownOp: true })
      }
      throw error
    }
  }

  /** Send one request exactly as the engine wrote it; the answer as an
   *  event document. */
  async function exchange (request) {
    const init = {
      method: request.method,
      headers: Array.isArray(request.headers) ? request.headers : [],
      redirect: 'manual'
    }
    if (typeof request.bodyBase64 === 'string') init.body = bytesOfBase64(request.bodyBase64)
    let reply
    try {
      reply = await wire(request.url, init)
    } catch (error) {
      return { error: error && error.message ? String(error.message) : String(error) }
    }
    const headers = []
    reply.headers.forEach((value, name) => { headers.push([name, value]) })
    const bytes = new Uint8Array(await reply.arrayBuffer())
    // The host's clock and random source, which the engine cannot reach: the
    // iat, exp, nonce and jti of a self-issued credential.
    const random = new Uint8Array(48)
    globalThis.crypto.getRandomValues(random)
    return {
      status: reply.status,
      headers,
      bodyBase64: base64OfBytes(bytes),
      now: Math.floor(Date.now() / 1000),
      randomBase64: base64OfBytes(random)
    }
  }

  /**
   * Run one operation to its end.
   *
   * @param {object} op `{ kind, url, ... }`; `body` may be a string or bytes
   * @returns {Promise<object>} the engine's `done` document
   */
  async function run (op) {
    let envelope = call('lwsClientStart', [JSON.stringify(opDocument(op)), JSON.stringify(session)])
    for (let step = 0; step < maxSteps; step += 1) {
      const action = envelope.action || {}
      if (action.fetch !== undefined) {
        const event = await exchange(action.fetch)
        envelope = call('lwsClientStep', [JSON.stringify(envelope.state), JSON.stringify(event)])
        continue
      }
      if (action.session !== undefined) session = action.session
      if (action.done !== undefined) return action.done
      throw new LwsClientError(action.fail)
    }
    throw new LwsClientError({ code: 'hostStepLimit', steps: maxSteps })
  }

  const with_ = (kind) => (url, args = {}) => run({ ...args, kind, url })

  return {
    engine,
    run,
    /** The session (access tokens and subject token), for a later client. */
    session: () => ({ ...session }),
    discover: with_('discover'),
    describe: with_('describe'),
    /** `read(url, { accept, rangeStart, rangeEnd, ifNoneMatch, prefer })` */
    read: with_('read'),
    readPage: with_('readPage'),
    head: with_('head'),
    /** `create(containerUrl, { body, mediaType, slug, container, types, links })` */
    create: with_('create'),
    /** `update(url, { body, mediaType, precondition, tag, ifNoneMatchTags, retry412, links })`;
     *  `ifNoneMatchTags` (entity tags, or field values of them) sends
     *  `If-None-Match`, alone or with the `If-Match` of `precondition` */
    update: with_('update'),
    patch: with_('patch'),
    /** `delete(url, { recursive, precondition, tag })` */
    delete: with_('delete'),
    findLinkset: with_('findLinkset'),
    readLinkset: with_('readLinkset'),
    /** `updateLinkset(resourceUrl, { body })`, or with `{ linksetUrl, body }`
     *  when the caller has the linkset resource. */
    updateLinkset: with_('updateLinkset'),
    putLinkset: with_('putLinkset'),
    /** `move(url, { destination })` */
    move: with_('move'),
    list: with_('list'),
    typeIndex: with_('typeIndex'),
    /** `search(anyUrlInTheStorage, { query })`, or `{ endpoint, query }` with
     *  the service endpoint, `{ onePage: true }` for one page */
    search: with_('search'),
    queryFormats: with_('queryFormats'),
    /** `subscribe(url, { topics, inbox, expires })`, or with `{ endpoint }`
     *  when the caller has the notification service endpoint: the
     *  subscription is POSTed to it with no discovery */
    subscribe: with_('subscribe'),
    getSubscription: with_('getSubscription'),
    unsubscribe: with_('unsubscribe'),
    /** `requestAccess(url, { policies: [{ actions, assignee, targets, constraint }], inbox })`,
     *  or one policy as `{ actions, assignee, targets, constraint }` */
    requestAccess: with_('requestAccess'),
    grantAccess: with_('grantAccess'),
    getAccess: with_('getAccess'),
    revokeAccess: with_('revokeAccess'),
    /** `verifyNotification(baseUrl, { requestTarget, method, headers, body, trustedStorages })`:
     *  the engine's verdict `{ accept, status, reason? }`. */
    verifyNotification: with_('verifyNotification')
  }
}

/**
 * A new `did:key` agent: the engine makes the key pair and the identifier from
 * 64 random bytes of this host's random source. The host reads none of it.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @param {string} [options.algorithm] the engine's name of the algorithm
 *   (default `ES256`, a P-256 key; `EdDSA` makes an Ed25519 key)
 * @returns {Promise<{agent: string, kid: string, selfIssued: object}>}
 *   `selfIssued` is the `createLwsClient` option of that name
 */
export async function createDidKey (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const algorithm = typeof options.algorithm === 'string' ? options.algorithm : 'ES256'
  const random = new Uint8Array(64)
  globalThis.crypto.getRandomValues(random)
  const answer = engine.call('lwsClientNewKey', [algorithm, base64OfBytes(random)])
  return answer.key
}

/**
 * An HTTP receiver for webhook notifications. For each request it asks the
 * engine (`verifyNotification`) and answers with the status of the
 * verdict; an accepted notification goes to `onNotification`. The receiver
 * reads no header and decides nothing.
 *
 * @param {object} options
 * @param {object} options.client a client from `createLwsClient`
 * @param {Function} [options.onNotification] `(verdict, bodyBytes, request)`
 * @param {number} [options.port] default 0 (an ephemeral port)
 * @param {string} [options.host] default 127.0.0.1
 * @returns {Promise<{ url: string, close: Function, received: Function }>}
 *   `url` is the receiver's base URL; any path under it receives
 */
export async function createNotificationReceiver (options) {
  const { createServer } = await import('node:http')
  const client = options.client
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  let base = ''
  const verdicts = []
  const server = createServer((request, response) => {
    const chunks = []
    request.on('data', (chunk) => chunks.push(chunk))
    request.on('end', async () => {
      const body = new Uint8Array(Buffer.concat(chunks))
      const headers = []
      for (let index = 0; index + 1 < request.rawHeaders.length; index += 2) {
        headers.push([request.rawHeaders[index], request.rawHeaders[index + 1]])
      }
      let verdict
      try {
        verdict = await client.verifyNotification(base, {
          requestTarget: request.url, method: request.method, headers, body
        })
      } catch (error) {
        response.statusCode = 500
        response.end()
        return
      }
      verdicts.push(verdict)
      if (verdict.accept === true && typeof options.onNotification === 'function') {
        try { options.onNotification(verdict, body, { target: request.url, headers }) } catch (_e) { /* the caller's */ }
      }
      response.statusCode = verdict.status
      response.end()
    })
  })
  await new Promise((resolve, reject) => {
    server.once('error', reject)
    server.listen(typeof options.port === 'number' ? options.port : 0, host, resolve)
  })
  base = `http://${host}:${server.address().port}/`
  return {
    url: base,
    received: () => verdicts.slice(),
    close: () => new Promise((resolve) => server.close(resolve))
  }
}
