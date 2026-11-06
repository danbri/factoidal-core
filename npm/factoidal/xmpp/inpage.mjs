// factoidal/xmpp/inpage.mjs — the Lean XMPP server with no network: it
// runs in the page (or a worker, or Node) beside the code that talks to it,
// and each connection is a pair of in-order message channels.
//
//   import { loadEngine } from '@factoidal/core/browser'
//   import { openInPageXmppServer, inPageWebSocket } from '@factoidal/core/xmpp/inpage'
//   const server = await openInPageXmppServer({ engine: await loadEngine(),
//     domain: 'foafos.local', mucDomain: 'rooms.foafos.local',
//     accounts: [{ username: 'shell', password }] })
//   const link = server.connect()            // { send(message), onmessage, close() }
//   const WS = inPageWebSocket(server)       // a WebSocket-shaped class for
//   new WS('xmpp-inpage:', 'xmpp')           //   Strophe.js and other RFC 7395 clients
//
// A message is one RFC 7395 message (https://www.rfc-editor.org/rfc/rfc7395):
// `<open/>` and `<close/>` in the framing namespace, then one complete
// element each. The engine's message carrier (`xmppMsgOpen`, `xmppMsgFeed`,
// `xmppMsgDeliver`, `xmppMsgClose`; Wasm/Ops/XmppSession.lean) makes every
// protocol decision; this file only moves messages and performs the routes
// (router.mjs, shared with the Node host). No Node or browser API beyond
// `crypto.getRandomValues` and `queueMicrotask`.
//
// There is no socket, so there is no Origin to check: whoever holds the
// server object can connect, and the accounts' passwords are what the
// engine checks (SCRAM-SHA-256). The host page decides which code gets it.

import { createXmppRouter } from './router.mjs'

/** Unpredictable values for the stream id and the SCRAM server nonce
 *  (RFC 6120 section 4.7.3, RFC 5802 section 5.1); the engine asks the host. */
function randomToken (bytes = 18) {
  const b = new Uint8Array(bytes)
  globalThis.crypto.getRandomValues(b)
  let s = ''
  for (const x of b) s += String.fromCharCode(x)
  return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '')
}

/**
 * @param {object} options
 * @param {object} options.engine a loaded engine handle (`loadEngine()`)
 * @param {string} [options.domain] default `localhost`
 * @param {Array<{username: string, password: string}>} [options.accounts]
 * @param {string} [options.mucDomain] XEP-0045 rooms (L4Factoidal/XMPP/Muc.lean)
 * @param {string} [options.mixDomain] XEP-0369 channels (L4Factoidal/XMPP/Mix.lean)
 * @param {string} [options.gc3Domain] GC3 prototype groups (L4Factoidal/XMPP/Gc3.lean)
 * @param {Function} [options.onError]
 */
export async function openInPageXmppServer (options = {}) {
  const engine = options.engine
  if (!engine || typeof engine.call !== 'function') throw new Error('openInPageXmppServer: options.engine is required')
  const onError = typeof options.onError === 'function' ? options.onError : (e) => console.error(`xmpp-inpage: ${e.message}`)
  const config = {}
  for (const k of ['domain', 'mucDomain', 'mixDomain', 'gc3Domain', 'saltB64']) {
    if (typeof options[k] === 'string') config[k] = options[k]
  }
  if (typeof config.saltB64 !== 'string') config.saltSeed = randomToken()
  config.occupantSeed = randomToken()
  if (Array.isArray(options.accounts)) config.accounts = options.accounts
  if (typeof options.iterationCount === 'number') config.iterationCount = options.iterationCount
  const opened = engine.call('xmppOpen', [JSON.stringify(config)])
  if (typeof opened.handle !== 'string') throw new Error('xmppOpen answered with no handle')
  const handle = opened.handle
  const router = createXmppRouter({ onError })
  let closed = false

  function connect () {
    if (closed) throw new Error('the in-page XMPP server is closed')
    const got = engine.call('xmppMsgOpen', [handle, JSON.stringify({ streamId: randomToken(), nonce: randomToken() })])
    if (typeof got.handle !== 'string') throw new Error('xmppMsgOpen answered with no handle (an engine without the message carrier?)')
    const session = got.handle
    let open = true
    // Messages to the client go out in order, never inside an engine call.
    const emit = (msgs) => {
      for (const m of msgs) {
        queueMicrotask(() => {
          if (typeof link.onmessage === 'function') {
            try { link.onmessage(m) } catch (error) { onError(error) }
          }
        })
      }
    }
    const end = () => {
      if (!open) return
      open = false
      router.connections.delete(c)
      let answer
      try { answer = engine.call('xmppMsgClose', [session]) } catch (error) { onError(error); answer = { send: [], routeFull: [] } }
      for (const r of answer.routeFull || []) router.routeFull(null, r.to, r.text, null)
      emit(answer.send || [])
      queueMicrotask(() => { if (typeof link.onclose === 'function') link.onclose() })
    }
    const c = {
      bare: null,
      full: null,
      deliver (text) {
        if (!open) return false
        const answer = engine.call('xmppMsgDeliver', [session, text])
        if (answer.delivered === true) { emit(answer.send); return true }
        return false
      }
    }
    router.connections.add(c)
    const link = {
      onmessage: null,
      onclose: null,
      get open () { return open },
      /** One whole RFC 7395 message from the client. */
      send (message) {
        if (!open) throw new Error('the in-page XMPP connection is closed')
        let answer
        try {
          // The rate limits read the host's clock.
          engine.call('xmppClock', [handle, String(Math.floor(Date.now() / 1000))])
          answer = engine.call('xmppMsgFeed', [session, String(message)])
        } catch (error) { onError(error); end(); return }
        emit(answer.send || [])
        router.apply(c, answer)
        if (answer.close === true) end()
      },
      close: end
    }
    return link
  }

  return {
    engine,
    handle,
    domain: typeof opened.domain === 'string' ? opened.domain : (config.domain || 'localhost'),
    mucDomain: config.mucDomain || null,
    connect,
    /** The live connections' `{bare, full}` pairs. */
    sessions () { return Array.from(router.connections, (c) => ({ bare: c.bare, full: c.full })) },
    close () {
      if (closed) return
      closed = true
      for (const c of Array.from(router.connections)) router.connections.delete(c)
      try { engine.call('xmppClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/**
 * A WebSocket-shaped class whose instances are connections to `server`, so
 * an RFC 7395 client written for `WebSocket` (Strophe.js, the foafos XmppWs
 * client) runs unchanged. The URL is not used; the subprotocol is `xmpp`.
 */
export function inPageWebSocket (server) {
  return class InPageWebSocket {
    static CONNECTING = 0
    static OPEN = 1
    static CLOSING = 2
    static CLOSED = 3
    constructor (url, protocols) {
      this.url = String(url)
      this.protocol = 'xmpp'
      this.readyState = 0
      this.binaryType = 'blob'
      this.bufferedAmount = 0
      this.extensions = ''
      this.onopen = this.onmessage = this.onclose = this.onerror = null
      this._listeners = { open: [], message: [], close: [], error: [] }
      const wanted = Array.isArray(protocols) ? protocols : (protocols === undefined ? [] : [protocols])
      queueMicrotask(() => {
        if (wanted.length > 0 && !wanted.includes('xmpp')) { this._fail(); return }
        try { this._link = server.connect() } catch (_error) { this._fail(); return }
        this._link.onmessage = (data) => this._fire('message', { type: 'message', data, target: this })
        this._link.onclose = () => this._closed(1000)
        this.readyState = 1
        this._fire('open', { type: 'open', target: this })
      })
    }
    addEventListener (type, fn) { this._listeners[type]?.push(fn) }
    removeEventListener (type, fn) {
      const l = this._listeners[type]
      if (l) { const i = l.indexOf(fn); if (i >= 0) l.splice(i, 1) }
    }
    dispatchEvent (event) { this._fire(event.type, event); return true }
    send (data) {
      if (this.readyState !== 1) throw new Error('InvalidStateError: the connection is not open')
      this._link.send(String(data))
    }
    close (code = 1000) {
      if (this.readyState >= 2) return
      this.readyState = 2
      this._link?.close()
      if (!this._link) this._closed(code)
    }
    _fail () {
      this._fire('error', { type: 'error', target: this })
      this._closed(1006)
    }
    _closed (code) {
      if (this.readyState === 3) return
      this.readyState = 3
      this._fire('close', { type: 'close', code, reason: '', wasClean: code === 1000, target: this })
    }
    _fire (type, event) {
      const prop = this['on' + type]
      if (typeof prop === 'function') prop.call(this, event)
      for (const fn of [...(this._listeners[type] || [])]) fn.call(this, event)
    }
  }
}
