// factoidal/xmpp/server.mjs — a Node host for the Lean XMPP server
// (`formal/lean4/L4Factoidal/XMPP/`), through the wasm session ops of
// `formal/lean4/Wasm/Ops/XmppSession.lean`.
//
// This file is a socket, a UTF-8 decoder and a routing table. Every
// protocol decision — what answers a stream header, whether a password
// is right, where a stanza goes, what a roster looks like as bytes —
// is made by `L4Factoidal.XMPP.Server.step` inside the engine and
// reaches this file as the `send`/`route`/`presence`/`close` members of
// one `xmppSessionFeed` answer. Iron rule 7 of `CLAUDE.md`: no protocol
// logic in a host. What this host does instead, and the native harness
// (`formal/lean4/Harness/XmppServe.lean`) does with files:
//
//   * one engine session per TCP (or direct-TLS, XEP-0368) connection;
//   * `startTls` → the engine sent `<proceed/>` (RFC 6120 section 5.4.2.3):
//     stop reading in clear, run the TLS handshake on the same socket as
//     the server, and call `xmppSessionTlsUp` when it finishes. The
//     engine has already discarded every byte that arrived after
//     `<starttls/>`; this host also drops its UTF-8 decoder's tail;
//   * `route` → find the sessions bound to that bare JID and call
//     `xmppSessionDeliver` on each; none bound → hold the stanza in
//     memory until one binds (`xmppSessionDeliver` itself refuses an
//     unbound session, so nothing is destroyed on the way);
//   * `rostersSaved` → fetch the roster bytes with `xmppRosterGet` and
//     write them under DIR/roster/, unread, so a restart gets them back
//     through `xmppRosterSet`;
//   * DIR/spool/<bare jid>/<file> → the harness's mailbox layout, polled
//     for bound sessions and delivered, so a process that is not an XMPP
//     client (a web application, say) can hand a stanza to a user by
//     writing a file, exactly as it can with the native carrier.
//
// The wasm contract (`xmppOpen`, `xmppSessionOpen`, `xmppSessionFeed`,
// `xmppSessionDeliver`, `xmppSessionClose`, `xmppRosterGet`,
// `xmppRosterSet`, `xmppClose`) is stated in the Lean module's header.
//
// Not implemented, said here rather than left to be discovered:
// server-to-server federation, and any limit on how many bytes
// a client may send without completing a unit beyond `maxBuffered`,
// which is a transport limit this host applies by closing the socket.
// The other transport limits are `maxConnections`, `loginTimeoutMs` and
// `maxQueuedBytes`. There is no limit per address: behind a proxy, every
// client has the same one.

import { randomBytes } from 'node:crypto'
import { StringDecoder } from 'node:string_decoder'
import { mkdir, readFile, writeFile, readdir, unlink, rename } from 'node:fs/promises'
import { join } from 'node:path'
import { loadEngine } from '../bin/engine.mjs'
import { createXmppRouter } from './router.mjs'

/** The ops this host needs from the engine. */
export const XMPP_SERVER_OPS = [
  'xmppOpen', 'xmppClose',
  'xmppSessionOpen', 'xmppSessionFeed', 'xmppSessionDeliver', 'xmppSessionClose',
  'xmppSessionTlsUp', 'xmppRosterGet', 'xmppRosterSet', 'xmppWsOpen', 'xmppStateLoad', 'xmppClock'
]

/** An error raised by this host, as opposed to one the engine reported.
 *  `unknownOp` is set when the loaded WebAssembly module does not carry
 *  the operation at all, which is what a test skips on and what the CLI
 *  reports as "not yet wired". */
export class XmppHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'XmppHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/**
 * Whether the loaded engine carries the XMPP server operations.
 *
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{available: boolean, missing: string[]}>}
 */
export async function xmppServerOpsAvailable (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  let names
  try {
    names = engine.call('ops', []).ops
  } catch (_error) {
    return { available: false, missing: XMPP_SERVER_OPS.slice() }
  }
  const missing = XMPP_SERVER_OPS.filter((op) => !names.includes(op))
  return { available: missing.length === 0, missing }
}

/** A bare JID as one path segment: the harness's `pathSafe`
 *  (`Harness/XmppServe.lean`), so the two hosts share a state directory.
 *  Every byte that is not a letter, a digit, `.`, `-` or `_` is written
 *  as `%` and two lowercase hex digits. */
export function pathSafe (s) {
  let out = ''
  for (const byte of Buffer.from(s, 'utf8')) {
    const ch = String.fromCharCode(byte)
    if (byte < 0x80 && /[A-Za-z0-9._-]/.test(ch)) out += ch
    else out += '%' + byte.toString(16).padStart(2, '0')
  }
  return out
}

/** Unpredictable values for the stream id and the SCRAM server nonce
 *  (RFC 6120 section 4.7.3, RFC 5802 section 5.1). The engine has no
 *  random source and asks the host for both. */
function randomToken (bytes = 18) {
  return randomBytes(bytes).toString('base64url')
}

/**
 * Open one XMPP server on the engine and return the handle plus the
 * calls a host makes against it.
 *
 * @param {object} options
 * @param {string} [options.domain] the domain the server is authoritative for (default `localhost`)
 * @param {Array<{username: string, password: string}>} [options.accounts]
 * @param {string} [options.accountsText] `user:password` lines, the harness's accounts-file format
 * @param {string} [options.saltB64] the SCRAM salt, base64
 * @param {number} [options.iterationCount] the SCRAM iteration count
 * @param {boolean} [options.tlsCarrier] whether the carrier terminates TLS
 * @param {boolean} [options.disableRateLimits] no failed SASL login limit and no sender rate on
 *   held stanzas (`--dangerously-disable-ratelimits`)
 * @param {object} [options.heldLimits] caps of the stanzas held for offline accounts, each a
 *   number: `perAccount`, `perAccountBytes`, `total`, `totalBytes`, `senderPerWindow`,
 *   `senderWindow` (seconds); what is absent keeps the engine's default
 * @param {object} [options.engine] an engine handle to reuse
 * @returns {Promise<{engine: object, handle: string, domain: string,
 *   openSession: Function, roster: Function, setRoster: Function, close: Function}>}
 */
export async function openXmppServer (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const config = {}
  if (typeof options.domain === 'string') config.domain = options.domain
  if (Array.isArray(options.accounts)) config.accounts = options.accounts
  if (typeof options.accountsText === 'string') config.accountsText = options.accountsText
  if (typeof options.saltB64 === 'string') config.saltB64 = options.saltB64
  if (typeof options.iterationCount === 'number') config.iterationCount = options.iterationCount
  if (typeof options.tlsCarrier === 'boolean') config.tlsCarrier = options.tlsCarrier
  // XEP-0045 room service (L4Factoidal/XMPP/Muc.lean); off unless named.
  if (typeof options.mucDomain === 'string') config.mucDomain = options.mucDomain
  // Members-only rooms: [{room, members: [bare JID]}]; no list, an open room.
  if (Array.isArray(options.mucMembers)) config.mucMembers = options.mucMembers
  // XEP-0369 channels (L4Factoidal/XMPP/Mix.lean), joined through MIX-PAM; off unless named.
  if (typeof options.mixDomain === 'string') config.mixDomain = options.mixDomain
  // GC3 prototype groups (L4Factoidal/XMPP/Gc3.lean; no published spec); off unless named.
  if (typeof options.gc3Domain === 'string') config.gc3Domain = options.gc3Domain
  // The host keeps the state across restarts (a state key and a DIR): only
  // then does the engine produce `store`/`unstore`.
  if (options.persist === true) config.persist = true
  // The failed SASL login limit is on unless the operator turns it off
  // (https://github.com/danbri/factoidal/issues/1128); the engine decides.
  if (options.disableRateLimits === true) config.disableRateLimits = true
  if (options.heldLimits && typeof options.heldLimits === 'object') config.heldLimits = options.heldLimits
  let opened
  try {
    opened = engine.call('xmppOpen', [JSON.stringify(config)])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new XmppHostError(
        'the loaded l4factoidal WebAssembly module does not carry xmppOpen',
        { unknownOp: true })
    }
    throw error
  }
  if (typeof opened.handle !== 'string' || opened.handle.length === 0) {
    throw new XmppHostError('xmppOpen answered with no handle')
  }
  const handle = opened.handle
  // The rate limits read the host's clock: tell the engine when the second changes.
  let lastSecond = 0
  const tick = () => {
    const now = Math.floor(Date.now() / 1000)
    if (now === lastSecond) return
    lastSecond = now
    try {
      engine.call('xmppClock', [handle, String(now)])
    } catch (error) {
      // An older engine has no such op, and no limit that reads it.
      if (!isUnknownOp(error)) throw error
    }
  }
  // An older engine ignores the list, and the rooms would be open: do not start.
  if (Array.isArray(options.mucMembers) && opened.mucMembers !== options.mucMembers.length) {
    engine.call('xmppClose', [handle])
    throw new XmppHostError('this engine does not carry members-only rooms; rebuild the engine')
  }
  return {
    engine,
    handle,
    domain: typeof opened.domain === 'string' ? opened.domain : (config.domain || 'localhost'),
    accounts: typeof opened.accounts === 'number' ? opened.accounts : undefined,
    /** The engine's start warnings (--dangerously-disable-ratelimits). */
    warnings: Array.isArray(opened.warnings) ? opened.warnings : [],
    tick,
    /**
     * One client connection.
     * `remoteAddress` (the socket's) and the clock go to the engine for the
     * failed SASL login limit (https://github.com/danbri/factoidal/issues/1128).
     * @param {{streamId?: string, nonce?: string, tlsCarrier?: boolean, startTls?: boolean, maxUnits?: number, remoteAddress?: string}} [sessionOptions]
     */
    openSession (sessionOptions = {}) {
      const record = {
        streamId: typeof sessionOptions.streamId === 'string' ? sessionOptions.streamId : randomToken(),
        nonce: typeof sessionOptions.nonce === 'string' ? sessionOptions.nonce : randomToken(),
        now: Math.floor(Date.now() / 1000)
      }
      if (typeof sessionOptions.remoteAddress === 'string') record.remoteAddress = sessionOptions.remoteAddress
      if (typeof sessionOptions.tlsCarrier === 'boolean') record.tlsCarrier = sessionOptions.tlsCarrier
      if (typeof sessionOptions.startTls === 'boolean') record.startTls = sessionOptions.startTls
      if (typeof sessionOptions.maxUnits === 'number') record.maxUnits = sessionOptions.maxUnits
      const answer = engine.call('xmppSessionOpen', [handle, JSON.stringify(record)])
      if (typeof answer.handle !== 'string') throw new XmppHostError('xmppSessionOpen answered with no handle')
      const session = answer.handle
      let open = true
      return {
        handle: session,
        /** Feed received text; returns the engine's answer document. */
        feed (text) {
          tick()
          return engine.call('xmppSessionFeed', [session, text])
        },
        /** The TLS handshake a feed asked for (`startTls: true`) finished. */
        tlsUp () {
          return engine.call('xmppSessionTlsUp', [session])
        },
        /** Hand this session a stanza another session routed to it. */
        deliver (text) {
          return engine.call('xmppSessionDeliver', [session, text])
        },
        /** End of input: returns `{send: string[]}` and releases the handle. */
        close () {
          if (!open) return { send: [], routeFull: [] }
          open = false
          try {
            return engine.call('xmppSessionClose', [session])
          } catch (_error) {
            return { send: [], routeFull: [] }
          }
        }
      }
    },
    /** The roster of a bare JID: `{encoded, items}`. */
    roster (bare) {
      return engine.call('xmppRosterGet', [handle, bare])
    },
    /** Load a roster the host persisted (the `encoded` of `roster()`). */
    setRoster (bare, encoded) {
      engine.call('xmppRosterSet', [handle, bare, encoded])
    },
    close () {
      try { engine.call('xmppClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** Load `DIR/accounts` (one `user:password` per line) if it exists. */
async function readAccountsFile (path) {
  try {
    return await readFile(path, 'utf8')
  } catch (error) {
    if (error && error.code === 'ENOENT') return null
    throw error
  }
}

/**
 * A `net.Server` (or `tls.Server`, when `cert` and `key` are given —
 * XEP-0368 direct TLS) that runs one engine session per connection.
 *
 * The server is returned unlistened: the caller chooses the port.
 *
 * @param {object} options as `openXmppServer`, plus:
 * @param {string} [options.dir] state directory: `accounts` is read from it when
 *   no accounts are given; rosters are persisted under `roster/`; `spool/` is
 *   polled for stanzas written by other processes
 * @param {string|Buffer} [options.cert] PEM certificate chain for direct TLS
 * @param {string|Buffer} [options.key] PEM private key for direct TLS
 * @param {boolean} [options.startTls] listen in clear and use `cert` and
 *   `key` for STARTTLS (RFC 6120 section 5), which the engine then requires
 *   before anything else; without it, `cert` and `key` mean direct TLS
 * @param {number} [options.directTlsPort] with `startTls`, `listen` also serves
 *   XEP-0368 direct TLS on this port, in the same server: one set of rooms
 * @param {number} [options.pollMs] spool poll interval (default 250; 0 disables)
 * @param {number} [options.maxBuffered] residual UTF-8 bytes held by the engine
 *   after a feed before the socket is closed (default 1 MiB); the decoder
 *   may separately hold up to three bytes of an incomplete UTF-8 sequence
 * @param {number} [options.maxConnections] open connections, of all kinds, before
 *   a new one is closed at once (default 1024)
 * @param {number} [options.loginTimeoutMs] how long a connection may stay
 *   without a bound resource before it is closed (default 30000; 0 disables)
 * @param {number} [options.maxQueuedBytes] bytes waiting to be written to a
 *   client that is not reading, before the socket is closed (default 8 MiB)
 * @param {Function} [options.onError]
 * @param {Function} [options.onLog]
 * @returns {Promise<{server: object, xmpp: object, close: Function, sessions: Function}>}
 */
export async function createXmppServer (options = {}) {
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`xmpp-serve: ${error.message}`) }
  const onLog = typeof options.onLog === 'function' ? options.onLog : () => {}
  const dir = typeof options.dir === 'string' ? options.dir : null
  const pollMs = typeof options.pollMs === 'number' ? options.pollMs : 250
  const maxBuffered = typeof options.maxBuffered === 'number' ? options.maxBuffered : 1024 * 1024
  const limit = (name, fallback) => {
    const value = typeof options[name] === 'number' ? options[name] : fallback
    if (!Number.isSafeInteger(value) || value < 0) throw new XmppHostError(`${name} must be a nonnegative safe integer`)
    return value
  }
  const maxConnections = limit('maxConnections', 1024)
  const loginTimeoutMs = limit('loginTimeoutMs', 30000)
  const maxQueuedBytes = limit('maxQueuedBytes', 8 * 1024 * 1024)
  if (!Number.isSafeInteger(maxBuffered) || maxBuffered < 0) {
    throw new XmppHostError('maxBuffered must be a nonnegative safe integer')
  }
  if ((options.cert !== undefined) !== (options.key !== undefined)) {
    throw new XmppHostError('direct TLS requires both cert and key')
  }

  const serverOptions = { ...options }
  if (dir !== null && !Array.isArray(options.accounts) && typeof options.accountsText !== 'string') {
    const text = await readAccountsFile(join(dir, 'accounts'))
    if (text !== null) serverOptions.accountsText = text
  }
  const haveKey = options.cert !== undefined && options.key !== undefined
  if (options.startTls === true && !haveKey) {
    throw new XmppHostError('STARTTLS requires both cert and key')
  }
  const startTls = options.startTls === true
  const useTls = haveKey && !startTls
  if (typeof serverOptions.tlsCarrier !== 'boolean') serverOptions.tlsCarrier = useTls
  if (dir !== null && options.stateKey !== undefined) serverOptions.persist = true
  const xmpp = await openXmppServer(serverOptions)

  // Rosters the previous run persisted.
  try {
    if (dir !== null) {
      await mkdir(join(dir, 'roster'), { recursive: true })
      await mkdir(join(dir, 'spool'), { recursive: true })
      for (const name of await readdir(join(dir, 'roster'))) {
        if (!name.endsWith('.tsv')) continue
        try {
          const bare = decodeURIComponent(name.slice(0, -4))
          xmpp.setRoster(bare, await readFile(join(dir, 'roster', name), 'utf8'))
        } catch (error) {
          onError(new XmppHostError(`roster ${name}: ${error.message}`))
        }
      }
    }
  } catch (error) {
    xmpp.close()
    throw error
  }

  // The server's state across a restart (issue 1237): rosters, stanzas held
  // for offline accounts, MIX channels and GC3 groups, as resources under
  // /xmpp/ of an LWS storage kept in DIR/state, sealed under the state key,
  // opened IN-PROCESS as the component principal (issue 1238: no token, no
  // listener, Web Access Control decides). The engine says what to write
  // (`store`, `unstore`); this host only performs it. A wrong key or an item
  // that does not decode stops the start: it never starts empty.
  let state = null
  let stateWrites = Promise.resolve()
  let stateError = null
  if (dir !== null && options.stateKey !== undefined) {
    try {
      const { openLwsStorage } = await import('../lws/server.mjs')
      const base = 'https://xmpp-state.invalid/'
      const principal = 'urn:factoidal:component:xmpp-serve'
      state = await openLwsStorage({
        engine: xmpp.engine, baseIri: base, dir: join(dir, 'state'), storage: 'files',
        storageKey: options.stateKey, principal, realClock: true, lockCommand: 'xmpp-serve',
        // Absolute IRIs, which never depended on the base (relative ones work
        // since issue https://github.com/danbri/factoidal/issues/1241 was fixed).
        rootAcl: `@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n<${base}.acl#xmpp> a acl:Authorization ;\n` +
          `  acl:agent <${principal}> ;\n  acl:accessTo <${base}> ;\n  acl:default <${base}> ;\n` +
          '  acl:mode acl:Read, acl:Write, acl:Control .\n'
      })
      const get = (target, accept) => state.step({ method: 'GET', target, headers: accept ? [['Accept', accept]] : [], body: new Uint8Array(0) })
      for (const kind of ['roster', 'held', 'mix', 'gc3']) {
        const listing = await get(`/xmpp/${kind}/`, 'application/lws+json')
        if (listing.status === 404) continue
        if (listing.status !== 200) throw new XmppHostError(`state: listing /xmpp/${kind}/ answered ${listing.status}`)
        const doc = JSON.parse(new TextDecoder().decode(listing.body))
        for (const item of doc.items || []) {
          const path = '/' + String(item.id).slice(base.length)
          const got = await get(path)
          if (got.status !== 200) throw new XmppHostError(`state: ${path} answered ${got.status}`)
          const loaded = xmpp.engine.call('xmppStateLoad', [xmpp.handle, path, new TextDecoder().decode(got.body)])
          if (loaded === null || typeof loaded !== 'object') throw new XmppHostError(`state: ${path} was refused`)
        }
      }
    } catch (error) {
      try { state?.close() } catch (_error) { /* already closed */ }
      xmpp.close()
      throw error instanceof XmppHostError ? error : new XmppHostError(`state: ${error.message}`)
    }
  }
  const hexOf = (s) => Buffer.from(s, 'utf8').toString('hex')
  /** Perform the engine's `store` / `unstore`, in order, one at a time. */
  function persistState (answer) {
    if (state === null) return
    const stores = Array.isArray(answer.store) ? answer.store : []
    const unstores = Array.isArray(answer.unstore) ? answer.unstore : []
    if (stores.length === 0 && unstores.length === 0) return
    stateWrites = stateWrites.then(async () => {
      for (const { path, text } of stores) {
        const r = await state.step({ method: 'PUT', target: path, headers: [['Content-Type', 'text/plain; charset=utf-8']], body: new TextEncoder().encode(text) })
        if (r.status >= 300) throw new XmppHostError(`state: PUT ${path} answered ${r.status}`)
      }
      for (const path of unstores) {
        const r = await state.step({ method: 'DELETE', target: path, headers: [], body: new Uint8Array(0) })
        if (r.status >= 300 && r.status !== 404) throw new XmppHostError(`state: DELETE ${path} answered ${r.status}`)
      }
    }).catch((error) => { stateError = error; onError(error) })
  }
  // Migration: plaintext roster files of an earlier run go into the sealed
  // state, then the plaintext files are deleted.
  if (state !== null) {
    for (const name of await readdir(join(dir, 'roster')).catch(() => [])) {
      if (!name.endsWith('.tsv')) continue
      const bare = decodeURIComponent(name.slice(0, -4))
      const { encoded } = xmpp.roster(bare)
      persistState({ store: [{ path: `/xmpp/roster/${hexOf(bare)}`, text: encoded }] })
      await stateWrites
      if (stateError === null) await unlink(join(dir, 'roster', name)).catch(() => {})
    }
  }

  // The routing table (router.mjs, shared with the in-page host): every live
  // connection, with the last `bare`/`full` the engine reported, and the
  // bounded fallback queue for stanzas routed to a session that closed.
  const router = createXmppRouter({ onError: (error) => onError(new XmppHostError(error.message)) })
  const { connections, pending, boundTo, routeFull } = router
  // Raw transports also include TLS peers that have not reached the secure
  // connection callback and therefore have no engine session yet.
  const transports = new Set()

  // Transport limits, like `maxBuffered`: bytes and time, not protocol.
  function closeIfBacklogged (c) {
    if (c.socket.destroyed || !(c.socket.writableLength > maxQueuedBytes)) return
    onError(new XmppHostError(`connection exceeded ${maxQueuedBytes} queued bytes`))
    c.socket.destroy()
  }

  function writeAll (c, lines) {
    for (const line of lines) if (!c.socket.destroyed) c.socket.write(line)
    closeIfBacklogged(c)
  }

  /** A connection gets `loginTimeoutMs` to bind a resource. */
  function startLoginTimer (c) {
    if (loginTimeoutMs === 0) return
    c.loginTimer = setTimeout(() => {
      if (c.full === null && connections.has(c)) {
        onLog('closing a connection that did not log in in time')
        c.socket.destroy()
      }
    }, loginTimeoutMs)
    c.loginTimer.unref()
  }

  /** Count a new socket, or close it at once if the server is full. */
  function admit (socket) {
    if (transports.size >= maxConnections) {
      onError(new XmppHostError(`refused a connection: ${maxConnections} are open`))
      socket.destroy()
      return
    }
    transports.add(socket)
    socket.once('close', () => transports.delete(socket))
  }

  let rosterWrites = Promise.resolve()
  let persistenceError = null
  function persistRosters (bares) {
    // With a state key the rosters are in the sealed state (`persistState`).
    if (dir === null || state !== null) return
    for (const bare of bares) {
      try {
        // Capture the engine's bytes at this feed, before another feed can
        // change the roster. Serialize writes; replace each file atomically.
        const { encoded } = xmpp.roster(bare)
        rosterWrites = rosterWrites.then(async () => {
          const path = join(dir, 'roster', pathSafe(bare) + '.tsv')
          const temporary = path + '.' + randomToken() + '.tmp'
          try {
            await writeFile(temporary, encoded, { flag: 'wx' })
            await rename(temporary, path)
          } finally {
            await unlink(temporary).catch(() => {})
          }
        }).catch(error => {
          persistenceError = new XmppHostError(`persisting roster of ${bare}: ${error.message}`)
          onError(persistenceError)
        })
      } catch (error) {
        persistenceError = new XmppHostError(`reading roster of ${bare}: ${error.message}`)
        onError(persistenceError)
      }
    }
  }

  /** Perform one feed answer. */
  function perform (c, answer) {
    persistState(answer)
    writeAll(c, answer.send)
    router.apply(c, answer)
    if (Array.isArray(answer.rostersSaved) && answer.rostersSaved.length > 0) {
      persistRosters(answer.rostersSaved)
    }
    if (answer.startTls === true && answer.close !== true) upgrade(c)
    if (answer.close === true) {
      c.closing = true
      c.socket.end()
    }
  }

  /** RFC 6120 section 5.4.3: the `<proceed/>` is already written. Stop
   *  reading in clear and become the TLS server on the same socket. */
  function upgrade (c) {
    c.upgrading = true
    const raw = c.socket
    raw.removeListener('data', c.onData)
    import('node:tls').then((tls) => {
      const secure = new tls.TLSSocket(raw, {
        isServer: true,
        secureContext: tls.createSecureContext({ cert: options.cert, key: options.key })
      })
      secure.once('secure', () => {
        let answer
        try { answer = c.session.tlsUp() } catch (error) { onError(error); answer = null }
        if (answer === null || answer.ok === false) {
          onError(new XmppHostError(`xmppSessionTlsUp refused: ${answer && answer.error}`))
          secure.destroy()
          endSession(c)
          return
        }
        c.socket = secure
        c.decoder = new StringDecoder('utf8')
        c.upgrading = false
        secure.on('data', c.onData)
      })
      secure.on('error', (error) => {
        onError(new XmppHostError(`STARTTLS handshake: ${error.message}`))
        secure.destroy()
        endSession(c)
      })
      secure.on('close', () => endSession(c))
    }).catch((error) => { onError(error); raw.destroy(); endSession(c) })
  }

  function endSession (c) {
    if (!connections.has(c)) return
    connections.delete(c)
    clearTimeout(c.loginTimer)
    let answer
    try { answer = c.session.close() } catch (error) { onError(error); answer = { send: [] } }
    // The session left its MUC rooms (Muc.leaveAll): tell the other occupants.
    for (const r of answer.routeFull || []) routeFull(c, r.to, r.text, null)
    if (!c.closing && !c.socket.destroyed) {
      writeAll(c, answer.send)
      if (answer.bytes instanceof Uint8Array && answer.bytes.length > 0) c.socket.write(answer.bytes)
      c.socket.end()
    }
  }

  function onConnection (socket, direct = false) {
    let session
    try {
      session = xmpp.openSession({ tlsCarrier: useTls || direct, startTls: startTls && !direct, remoteAddress: typeof socket.remoteAddress === 'string' ? socket.remoteAddress : '' })
    } catch (error) {
      onError(error)
      socket.destroy()
      return
    }
    const c = {
      socket,
      session,
      bare: null,
      full: null,
      closing: false,
      decoder: new StringDecoder('utf8'),
      deliver (text) {
        const answer = c.session.deliver(text)
        if (answer.delivered === true) { writeAll(c, answer.send); return true }
        return false
      }
    }
    connections.add(c)
    startLoginTimer(c)
    onLog(`connection from ${socket.remoteAddress}:${socket.remotePort}`)
    c.onData = (chunk) => {
      if (!connections.has(c) || c.closing || c.upgrading) return
      const text = c.decoder.write(chunk)
      if (text.length === 0) return
      let answer
      try {
        answer = session.feed(text)
        if (!Number.isSafeInteger(answer.bufferedBytes) || answer.bufferedBytes < 0) {
          throw new XmppHostError('xmppSessionFeed lacks a valid bufferedBytes result; rebuild the engine')
        }
      } catch (error) {
        onError(error)
        socket.destroy()
        endSession(c)
        return
      }
      // A transport limit, not a protocol one: a client that sends this
      // much without completing a unit is cut off.
      perform(c, answer)
      if (answer.bufferedBytes > maxBuffered) {
        onError(new XmppHostError(`connection exceeded ${maxBuffered} buffered bytes`))
        socket.destroy()
        endSession(c)
      }
    }
    socket.on('data', c.onData)
    socket.on('end', () => endSession(c))
    socket.on('close', () => endSession(c))
    socket.on('error', (error) => {
      if (error && error.code !== 'ECONNRESET') onError(error)
      endSession(c)
    })
  }

  // XMPP over WebSocket (RFC 7395): every byte goes to xmppWsFeed, which
  // does the HTTP handshake, the frames and Server.step; this host writes
  // the bytes it is given and performs route/presence/rostersSaved as for TCP.
  const ws = options.websocket && typeof options.websocket === 'object' ? options.websocket : null
  function wsCall (op, args, bytes) {
    const got = xmpp.engine.callBlobIO(op, args, bytes)
    return { envelope: got.envelope, bytes: got.bytes instanceof Uint8Array ? got.bytes : new Uint8Array(0) }
  }
  function onWsConnection (socket) {
    let handle
    try {
      const opened = xmpp.engine.call('xmppWsOpen', [xmpp.handle, JSON.stringify({
        streamId: randomToken(), nonce: randomToken(),
        path: typeof ws.path === 'string' ? ws.path : '/xmpp-websocket',
        allowedOrigins: Array.isArray(ws.allowedOrigins) ? ws.allowedOrigins : [],
        allowNoOrigin: ws.allowNoOrigin === true,
        tlsCarrier: ws.cert !== undefined && ws.key !== undefined
      })])
      handle = opened.handle
    } catch (error) {
      onError(error)
      socket.destroy()
      return
    }
    const c = {
      socket,
      bare: null,
      full: null,
      closing: false,
      session: {
        close () {
          try {
            const got = wsCall('xmppWsClose', [handle], new Uint8Array(0))
            return { send: [], bytes: got.bytes, routeFull: got.envelope.routeFull || [] }
          } catch (_error) { return { send: [] } }
        }
      },
      deliver (text) {
        const got = wsCall('xmppWsDeliver', [handle, text], new Uint8Array(0))
        if (got.envelope.delivered === true) { if (!socket.destroyed) socket.write(got.bytes); closeIfBacklogged(c); return true }
        return false
      }
    }
    connections.add(c)
    startLoginTimer(c)
    socket.on('data', (chunk) => {
      if (!connections.has(c) || c.closing) return
      let got
      try {
        xmpp.tick()
        got = wsCall('xmppWsFeed', [handle], new Uint8Array(chunk.buffer, chunk.byteOffset, chunk.byteLength))
      } catch (error) {
        onError(error)
        socket.destroy()
        endSession(c)
        return
      }
      if (got.bytes.length > 0 && !socket.destroyed) socket.write(got.bytes)
      perform(c, { ...got.envelope, send: [] })
      if (got.envelope.bufferedBytes > maxBuffered) {
        onError(new XmppHostError(`connection exceeded ${maxBuffered} buffered bytes`))
        socket.destroy()
        endSession(c)
      }
    })
    socket.on('end', () => endSession(c))
    socket.on('close', () => endSession(c))
    socket.on('error', (error) => {
      if (error && error.code !== 'ECONNRESET') onError(error)
      endSession(c)
    })
  }
  let wsServer = null
  if (ws !== null) {
    if ((ws.cert !== undefined) !== (ws.key !== undefined)) {
      xmpp.close()
      throw new XmppHostError('the WebSocket listener needs both cert and key for TLS')
    }
    if (ws.cert !== undefined) {
      const tls = await import('node:tls')
      wsServer = tls.createServer({ cert: ws.cert, key: ws.key }, onWsConnection)
    } else {
      const net = await import('node:net')
      wsServer = net.createServer(onWsConnection)
    }
    wsServer.on('connection', admit)
  }

  let server
  try {
    if (useTls) {
      const tls = await import('node:tls')
      server = tls.createServer({ cert: options.cert, key: options.key }, (socket) => onConnection(socket))
    } else {
      const net = await import('node:net')
      server = net.createServer((socket) => onConnection(socket))
    }
  } catch (error) {
    xmpp.close()
    throw error
  }
  server.on('connection', admit)

  // XEP-0368 direct TLS beside a STARTTLS listener: the engine takes its
  // answer per session, so this differs only in what `onConnection` passes.
  let directServer = null
  if (startTls && options.directTlsPort !== undefined) {
    const tls = await import('node:tls')
    directServer = tls.createServer({ cert: options.cert, key: options.key }, (socket) => onConnection(socket, true))
    directServer.on('connection', admit)
  }

  // The harness's mailbox: `<dir>/spool/<bare jid>/<name>` holds one
  // stanza's bytes for that account. Polled for every bound session,
  // delivered in name order, unlinked once the engine accepted it.
  let poller = null
  let polling = false
  let pollTask = Promise.resolve()
  async function pollSpool () {
    if (polling || dir === null) return
    polling = true
    try {
      const bares = new Set()
      for (const c of connections) if (c.full !== null) bares.add(c.bare)
      for (const bare of bares) {
        const box = join(dir, 'spool', pathSafe(bare))
        let names
        try { names = (await readdir(box)).sort() } catch (_error) { continue }
        for (const name of names) {
          const path = join(box, name)
          let text
          try { text = await readFile(path, 'utf8') } catch (_error) { continue }
          const targets = boundTo(bare)
          if (targets.length === 0) break
          let accepted = false
          for (const t of targets) {
            try {
              if (t.deliver(text)) accepted = true
            } catch (error) { onError(error) }
          }
          if (accepted) await unlink(path).catch(() => {})
        }
      }
    } finally {
      polling = false
    }
  }
  if (dir !== null && pollMs > 0) {
    poller = setInterval(() => {
      if (!polling) pollTask = pollSpool().catch(onError)
    }, pollMs)
    if (typeof poller.unref === 'function') poller.unref()
  }

  let closePromise = null
  return {
    server,
    wsServer,
    directServer,
    xmpp,
    /** The live connections' `{bare, full}` pairs, for a host's own view. */
    sessions () {
      return Array.from(connections, (c) => ({ bare: c.bare, full: c.full }))
    },
    /** Stanzas held for accounts with no bound session. */
    pending () {
      return new Map(pending)
    },
    close () {
      if (closePromise !== null) return closePromise
      closePromise = (async () => {
        if (poller !== null) clearInterval(poller)
        for (const c of Array.from(connections)) {
          endSession(c)
          c.socket.destroy()
        }
        for (const socket of transports) socket.destroy()
        try {
          await new Promise(resolve => server.close(resolve))
          if (wsServer !== null) await new Promise(resolve => wsServer.close(resolve))
          if (directServer !== null) await new Promise(resolve => directServer.close(resolve))
          await pollTask
          await rosterWrites
          await stateWrites
          if (persistenceError !== null) throw persistenceError
          if (stateError !== null) throw stateError
        } finally {
          try { state?.close() } catch (_error) { /* already closed */ }
          xmpp.close()
        }
      })()
      return closePromise
    }
  }
}

/**
 * Start a server and resolve once it is listening.
 *
 * @param {object} options as `createXmppServer`, plus `port` and `host`
 * @returns {Promise<{server: object, xmpp: object, port: number, host: string,
 *   origin: string, close: Function, sessions: Function}>}
 */
export async function listen (options = {}) {
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const created = await createXmppServer(options)
  try {
    await new Promise((resolve, reject) => {
      created.server.once('error', reject)
      created.server.listen(port, host, resolve)
    })
  } catch (error) {
    await created.close()
    throw error
  }
  let wsOrigin = null
  if (created.wsServer !== null) {
    const wsPort = typeof options.websocket.port === 'number' ? options.websocket.port : 0
    try {
      await new Promise((resolve, reject) => {
        created.wsServer.once('error', reject)
        created.wsServer.listen(wsPort, host, resolve)
      })
    } catch (error) {
      await created.close()
      throw error
    }
    const wsScheme = options.websocket.cert !== undefined ? 'wss' : 'ws'
    const path = typeof options.websocket.path === 'string' ? options.websocket.path : '/xmpp-websocket'
    wsOrigin = `${wsScheme}://${host}:${created.wsServer.address().port}${path}`
  }
  let directOrigin = null
  if (created.directServer !== null) {
    try {
      await new Promise((resolve, reject) => {
        created.directServer.once('error', reject)
        created.directServer.listen(options.directTlsPort, host, resolve)
      })
    } catch (error) {
      await created.close()
      throw error
    }
    directOrigin = `xmpps://${host}:${created.directServer.address().port}`
  }
  const bound = created.server.address()
  const scheme = options.cert !== undefined && options.key !== undefined ? 'xmpps' : 'xmpp'
  return { ...created, port: bound.port, host, origin: `${scheme}://${host}:${bound.port}`, wsOrigin, directOrigin }
}
