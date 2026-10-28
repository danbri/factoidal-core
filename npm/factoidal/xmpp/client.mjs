// factoidal/xmpp/client.mjs — an OUTGOING XMPP client connection that
// serves HTTP over XMPP (XEP-0332) for a local HTTP request handler.
// https://github.com/danbri/factoidal/issues/1107 (step 1: `factoidal
// webdav-serve CONFIGDIR --xmpp JID`). Design record:
// docs/designissues/2026-10-28-http-over-xmpp.md.
//
// WHAT THIS FILE IS ALLOWED TO DO
// Open one TCP socket, or one direct-TLS socket (XEP-0368), to an XMPP
// server; give every text it reads to the engine (`xmppClientFeed`); write
// every text the engine answers (`send`); carry each HTTP request the engine
// names (`requests`) to the caller's `step` function (for webdav-serve, the
// same `step` that serves the HTTP listener) and give the response back
// (`xmppClientAnswer`); close the socket when the engine says `close`.
//
// It makes NO protocol decision. The stream negotiation, SASL SCRAM-SHA-256,
// the check of the server signature, resource binding, which stanza is an
// HTTP request, who may send one (the allow list), the refusals, chunked
// bodies and the response stanzas are decided in
// formal/lean4/L4Factoidal/XMPP/ClientStream.lean and HttpOverXmpp.lean
// (iron rule 7 of CLAUDE.md). The host supplies the SCRAM client nonce
// (random bytes) and moves bytes.
//
// THE WASM CONTRACT (formal/lean4/Wasm/Ops/XmppClient.lean)
//   xmppClientOpen   [configJson]                 -> { ok, handle, send }
//   xmppClientFeed   [handle, text]               -> { ok, send, requests, bound, close, reason, stage, bufferedBytes }
//   xmppClientAnswer [handle, id, responseJson]   -> { ok, send }
//   xmppClientClose  [handle]                     -> { ok, send }

import { randomBytes } from 'node:crypto'
import { StringDecoder } from 'node:string_decoder'
import { loadEngine } from '../bin/engine.mjs'

/** The ops this host needs from the engine. */
export const XMPP_CLIENT_OPS = ['xmppClientOpen', 'xmppClientFeed', 'xmppClientAnswer', 'xmppClientClose']

/** An error of this host, as opposed to one the engine reported. */
export class XmppClientError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'XmppClientError'
    this.unknownOp = detail.unknownOp === true
  }
}

function call (engine, op, args) {
  let envelope
  try {
    envelope = engine.call(op, args)
  } catch (error) {
    const text = error && error.message ? String(error.message) : String(error)
    if (text.indexOf('unknown op') >= 0) {
      throw new XmppClientError(`the loaded l4factoidal WebAssembly module does not carry ${op}`, { unknownOp: true })
    }
    throw error
  }
  if (envelope === null || typeof envelope !== 'object') throw new XmppClientError(`${op} answered with no envelope`)
  if (envelope.ok === false) throw new XmppClientError(`${op}: ${envelope.error}`)
  return envelope
}

/**
 * Connect to an XMPP server as `jid` and serve HTTP over XMPP with `step`.
 * Resolves once the resource is bound (or rejects with the engine's reason).
 *
 * @param {object} options
 * @param {string} options.jid the account, `user@domain` (a resource may follow `/`)
 * @param {string} options.password
 * @param {string} [options.host] the XMPP server's address (default: the JID's domain; no SRV lookup)
 * @param {number} [options.port] default 5222, or 5223 with `tls`
 * @param {boolean} [options.tls] direct TLS (XEP-0368); without it the engine allows plain TCP to a loopback address only
 * @param {object} [options.tlsOptions] passed to `tls.connect` (for example `ca`)
 * @param {string[]} [options.allow] bare JIDs that may send requests
 * @param {string} [options.resource]
 * @param {object[]} [options.mounts] the WebDAV handle's mounts, passed unread (the engine refuses writable local mounts without the opt-in)
 * @param {boolean} [options.dangerouslyAllowWritableWithoutLogin]
 * @param {Function} options.step `async ({method, target, headers, body}) => ({status, headers, body})`
 * @param {object} [options.engine]
 * @param {Function} [options.onError]
 * @param {number} [options.maxBuffered] residual bytes the engine may hold before the socket is closed (default 16 MiB)
 * @returns {Promise<{jid: string, closed: Promise<string>, close: Function}>}
 */
export async function connectHttpTarget (options = {}) {
  if (typeof options.step !== 'function') throw new XmppClientError('connectHttpTarget needs step')
  if (typeof options.jid !== 'string') throw new XmppClientError('connectHttpTarget needs jid')
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const onError = typeof options.onError === 'function' ? options.onError : () => {}
  const maxBuffered = typeof options.maxBuffered === 'number' ? options.maxBuffered : 16 * 1024 * 1024
  const config = {
    jid: options.jid,
    password: typeof options.password === 'string' ? options.password : '',
    clientNonce: randomBytes(24).toString('base64url'),
    allow: Array.isArray(options.allow) ? options.allow : []
  }
  config.tls = options.tls === true
  if (typeof options.host === 'string') config.host = options.host
  if (Array.isArray(options.mounts)) config.mounts = options.mounts
  if (options.dangerouslyAllowWritableWithoutLogin === true) config.dangerouslyAllowWritableWithoutLogin = true
  if (typeof options.resource === 'string') config.resource = options.resource
  if (typeof options.minIterations === 'number') config.minIterations = options.minIterations
  const opened = call(engine, 'xmppClientOpen', [JSON.stringify(config)])
  const handle = opened.handle
  const domain = opened.domain
  if (typeof domain !== 'string') throw new XmppClientError('xmppClientOpen answered with no domain; rebuild the engine')
  const host = opened.host
  const port = typeof options.port === 'number' ? options.port : (options.tls === true ? 5223 : 5222)

  let socket
  if (options.tls === true) {
    const tls = await import('node:tls')
    socket = tls.connect({ host, port, servername: domain, ...(options.tlsOptions || {}) })
  } else {
    const net = await import('node:net')
    socket = net.connect({ host, port })
  }

  let open = true
  let boundJid = null
  let resolveBound
  let rejectBound
  const bound = new Promise((resolve, reject) => { resolveBound = resolve; rejectBound = reject })
  let resolveClosed
  const closed = new Promise((resolve) => { resolveClosed = resolve })

  function write (texts) {
    for (const t of texts || []) if (!socket.destroyed) socket.write(t)
  }

  function finish (reason) {
    if (!open) return
    open = false
    try { call(engine, 'xmppClientClose', [handle]) } catch (_error) { /* already gone */ }
    if (!socket.destroyed) socket.end()
    if (boundJid === null) rejectBound(new XmppClientError(reason || 'the XMPP connection closed before binding'))
    resolveClosed(reason || '')
  }

  /** One request the engine named: carried to `step`, answered. */
  async function carry (request) {
    let answer
    try {
      const response = await options.step({
        method: request.method,
        target: request.target,
        headers: request.headers || [],
        body: new Uint8Array(Buffer.from(request.bodyBase64 || '', 'base64'))
      })
      answer = {
        status: response.status,
        headers: response.headers || [],
        bodyBase64: Buffer.from(response.body || new Uint8Array(0)).toString('base64')
      }
    } catch (error) {
      onError(error)
      answer = { status: 500, headers: [['content-type', 'text/plain']], bodyBase64: Buffer.from(`host error: ${error.message}\n`).toString('base64') }
    }
    if (!open) return
    try {
      write(call(engine, 'xmppClientAnswer', [handle, String(request.id), JSON.stringify(answer)]).send)
    } catch (error) {
      onError(error)
    }
  }

  const decoder = new StringDecoder('utf8')
  socket.on('connect', () => write(opened.send))
  socket.on('secureConnect', () => {})
  socket.on('data', (chunk) => {
    if (!open) return
    const text = decoder.write(chunk)
    if (text.length === 0) return
    let answer
    try {
      answer = call(engine, 'xmppClientFeed', [handle, text])
    } catch (error) {
      onError(error)
      socket.destroy()
      finish(error.message)
      return
    }
    write(answer.send)
    if (typeof answer.bound === 'string' && boundJid === null) {
      boundJid = answer.bound
      resolveBound(boundJid)
    }
    for (const r of answer.requests || []) carry(r)
    if (answer.close === true) finish(answer.reason)
    else if (answer.bufferedBytes > maxBuffered) {
      onError(new XmppClientError(`the server sent more than ${maxBuffered} bytes without completing a stanza`))
      finish('buffer limit')
    }
  })
  socket.on('error', (error) => { onError(error); finish(error.message) })
  socket.on('close', () => finish('the server closed the connection'))

  const jid = await bound
  return {
    jid,
    writableWithoutLogin: opened.writableWithoutLogin || [],
    closed,
    close () {
      if (open && !socket.destroyed) {
        try { write(call(engine, 'xmppClientClose', [handle]).send) } catch (_error) { /* gone */ }
      }
      finish('')
      return closed
    }
  }
}
