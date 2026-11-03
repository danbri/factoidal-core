// A Node HTTP host for the Factoidal WebDAV server.
// https://github.com/danbri/factoidal/issues/1066
// Design record: docs/designissues/2026-10-27-webdav.md
//
// WHAT THIS FILE IS ALLOWED TO DO
// Carry sockets, files and fetches for the engine, and nothing else:
//
// * at start, list CONFIGDIR and give the names to `webdavOpen`; read the
//   files and test the paths the engine names (`need`) and give them to
//   `webdavLoad` until it answers `ready`; write the files it names
//   (`write`, a key file it made); open each local storage directory it
//   names with the ops `lws-serve` uses (`openLwsStorage`, the config passed
//   unread);
// * per request, give the method, target, header fields and content to
//   `webdavStep`, then carry what the engine answers: an `lws` request to
//   the local storage it names (no socket: the storage handle's own step),
//   a `fetch` to the URL it names, until it answers a `response`, which
//   this file writes back; when the response carries `write` (the state
//   file `.webdav-state.json`: dead properties and locks), replace that file
//   first (a new file in the same directory, mode 0600, then a rename);
// * with a users file (`--users`, https://github.com/danbri/factoidal/issues/1108),
//   give its path to `webdavOpen` and the bytes the engine names; when the
//   engine answers `need` (a login: one PBKDF2-HMAC-SHA256 derivation), run
//   exactly that WebCrypto call (`answerCipherRequest`, lib/cipher-host.mjs)
//   and give the answer to `webdavResume`; give each request's client
//   address (the socket's `remoteAddress`) to `webdavStep`, for the
//   failed-login limit the engine keeps
//   (https://github.com/danbri/factoidal/issues/1119); pass the limit
//   options unread and print the `warnings` of `ready`;
// * with `--cert` and `--key`, listen with Node `https` (TLS) instead of
//   `http`;
// * with `--guest NAME` (https://github.com/danbri/factoidal/issues/1147),
//   pass the name unread: the engine decides that a request with no
//   credentials acts as that user, and which mounts each user reaches.
//
// Expert review of the login: https://github.com/danbri/factoidal/issues/1117
//
// It makes NO protocol decision. Which files are mounts, what a mount file
// says, every status code, header field, XML body, lock, property and path
// mapping, every login decision (which users file lines count, whether a
// password matches, the login cache, whether Basic may run on this address)
// is decided in formal/lean4/L4Factoidal/WebDAV/ (iron rule 7 of
// CLAUDE.md). The one status code written here is 500, for a failure of
// this host itself. Requests are served one at a time (a queue), because
// the engine keeps one request in flight per handle.
//
// THE WASM CONTRACT (formal/lean4/Wasm/Ops/WebDAV.lean)
//   webdavOpen   [configJson]                 -> { ok, handle, need }
//   webdavLoad   [handle, filesJson]          -> { ok, need } | { ok, ready }
//   webdavStep   [handle, requestJson] + body -> { ok, response [+ write] | lws | fetch | need } + body
//   webdavResume [handle, answerJson]  + body -> { ok, response | lws | fetch | need } + body
//   webdavClose  [handle]                     -> { ok }

import {
  readFileSync, readdirSync, writeFileSync, existsSync, openSync, writeSync, fsyncSync, closeSync, renameSync, unlinkSync
} from 'node:fs'
import { resolve as resolvePath, dirname, basename, join } from 'node:path'
import { loadEngine } from '../bin/engine.mjs'
import { openLwsStorage } from '../lws/server.mjs'
import { answerCipherRequest } from '../lib/cipher-host.mjs'

/** The ops this host needs from the engine. */
export const WEBDAV_OPS = ['webdavOpen', 'webdavLoad', 'webdavStep', 'webdavResume', 'webdavClose']

/** The most engine answers one request may take before this host gives up:
 *  a bound against a defective module, not a protocol rule. */
const MAX_HOPS = 100000

/** The most rounds of `need` at start: the engine names two. */
const MAX_LOADS = 8

/** An error of this host, as opposed to one the engine reported. */
export class WebdavHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'WebdavHostError'
    this.unknownOp = detail.unknownOp === true
    this.envelope = detail.envelope
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

/** Random bytes as base64. Pure I/O. */
function randomBase64 (size) {
  const bytes = new Uint8Array(size)
  globalThis.crypto.getRandomValues(bytes)
  return Buffer.from(bytes).toString('base64')
}

function nowSeconds () {
  return Math.floor(Date.now() / 1000)
}

/** One engine call; an `ok: false` envelope is thrown with the engine's words. */
function callEngine (engine, op, args) {
  let envelope
  try {
    envelope = engine.call(op, args)
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new WebdavHostError(`the loaded l4factoidal WebAssembly module does not carry ${op}`, { unknownOp: true })
    }
    throw error
  }
  return envelope
}

function blobCall (engine, op, args, bytes) {
  const got = engine.callBlobIO(op, args, bytes)
  const envelope = got.envelope
  if (envelope === null || typeof envelope !== 'object') throw new WebdavHostError(`${op} answered with no envelope`)
  if (envelope.ok === false) throw new WebdavHostError(`${op}: ${envelope.error}`, { envelope })
  return { envelope, bytes: got.bytes instanceof Uint8Array ? got.bytes : new Uint8Array(0) }
}

/** The files and paths the engine named, read and tested. Pure I/O. */
function gather (configDir, need) {
  const files = (need.read || []).map((name) => {
    try {
      return { name, text: readFileSync(resolvePath(configDir, name), 'utf8') }
    } catch (_error) {
      return { name, missing: true }
    }
  })
  const exists = (need.exists || []).map((path) => ({ path, present: existsSync(resolvePath(configDir, path)) }))
  return { files, exists }
}

/**
 * Replace a file the engine named (`write` on a response) atomically: write
 * a new file in the same directory, flush it, then rename it over the old
 * one, so a crash leaves the old text or the new text. Pure I/O.
 */
function replaceFile (configDir, write) {
  const target = resolvePath(configDir, write.path)
  const suffix = Buffer.from(globalThis.crypto.getRandomValues(new Uint8Array(6))).toString('hex')
  const temp = join(dirname(target), `.${basename(target)}.${process.pid}.${suffix}.tmp`)
  const fd = openSync(temp, 'wx', parseInt(write.mode, 8))
  try {
    writeSync(fd, write.text)
    fsyncSync(fd)
  } finally {
    closeSync(fd)
  }
  try {
    renameSync(temp, target)
  } catch (error) {
    try { unlinkSync(temp) } catch (_error) { /* already gone */ }
    throw error
  }
}

/**
 * Open a WebDAV server handle over the mount files of `configDir`.
 *
 * @param {object} options
 * @param {string} options.configDir the directory of mount files
 * @param {object} [options.engine] an engine handle to reuse
 * @param {string} [options.users] the users file (an absolute path, or one
 *   relative to configDir): the listener then needs a login
 * @param {boolean} [options.tls] the listener uses TLS
 * @param {string} [options.host] the address the listener binds
 * @param {string} [options.loginLimit] `--login-limit`, passed unread
 * @param {string} [options.loginWindow] `--login-window`, passed unread
 * @param {boolean} [options.disableRateLimits] `--dangerously-disable-ratelimits`
 * @param {string} [options.guest] `--guest NAME`: the user a request with no
 *   credentials acts as (passed unread)
 * @returns {Promise<{handle: string, mounts: object[], step: Function, close: Function}>}
 */
export async function openWebdav (options = {}) {
  if (typeof options.configDir !== 'string') throw new WebdavHostError('openWebdav needs configDir')
  const configDir = options.configDir
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const listing = readdirSync(configDir)
  const login = {
    users: typeof options.users === 'string' ? options.users : null,
    tls: options.tls === true,
    host: typeof options.host === 'string' ? options.host : '127.0.0.1',
    limit: typeof options.loginLimit === 'string' ? options.loginLimit : null,
    window: typeof options.loginWindow === 'string' ? options.loginWindow : null,
    disableRateLimits: options.disableRateLimits === true
  }
  // The guest user (issue 1147), passed unread; the engine checks it.
  if (typeof options.guest === 'string') login.guest = options.guest
  const config = { listing, entropy: randomBase64(32), now: nowSeconds(), login }
  // The Host and Origin guard of the HTTP listener (issue 1124): the bound
  // address and the operator's names and origins, passed unread
  // (L4Factoidal/HTTP/LocalGuard.lean decides).
  if (options.localGuard !== undefined && options.localGuard !== null) config.localGuard = options.localGuard
  let envelope = callEngine(engine, 'webdavOpen', [JSON.stringify(config)])
  if (envelope.ok === false) throw new WebdavHostError(envelope.error, { envelope })
  const handle = envelope.handle
  let loads = 0
  while (envelope.need !== undefined) {
    loads += 1
    if (loads > MAX_LOADS) throw new WebdavHostError('webdavLoad asked for files more often than a start may')
    envelope = callEngine(engine, 'webdavLoad', [handle, JSON.stringify(gather(configDir, envelope.need))])
    if (envelope.ok === false) throw new WebdavHostError(envelope.error, { envelope })
  }
  const ready = envelope.ready
  // A file the engine made (a new key): written once, never over a file.
  for (const w of ready.write || []) {
    writeFileSync(resolvePath(configDir, w.path), w.text, { mode: parseInt(w.mode, 8), flag: 'wx' })
  }
  // Each local storage, opened as lws-serve opens it; the config is the
  // engine's, passed unread.
  // Each takes the lock of its directory (one writing process per storage
  // directory, https://github.com/danbri/factoidal/issues/1135): a directory
  // that lws-serve or another webdav-serve holds stops the start, and the
  // locks of the mounts opened before it are released.
  const storages = new Map()
  const storageNotices = []
  try {
    for (const l of ready.local || []) {
      const storage = await openLwsStorage({ engine, dir: resolvePath(configDir, l.dir), ...l.config, realClock: true, lockCommand: 'webdav-serve' })
      storages.set(l.name, storage)
      for (const n of storage.notices || []) storageNotices.push(`mount ${l.name}: ${n}`)
    }
  } catch (error) {
    for (const s of storages.values()) s.close()
    try { engine.call('webdavClose', [handle]) } catch (_error) { /* already gone */ }
    if (error !== null && typeof error === 'object' && error.envelope !== undefined && !(error instanceof WebdavHostError)) {
      throw new WebdavHostError(error.envelope.error, { envelope: error.envelope })
    }
    throw error
  }

  /** Carry one `fetch` the engine named. Pure I/O. */
  async function exchange (request, bytes) {
    const init = { method: request.method, headers: request.headers || [], redirect: 'manual' }
    if (bytes.length > 0) init.body = bytes
    let reply
    try {
      reply = await fetch(request.url, init)
    } catch (error) {
      return { answer: { error: error && error.message ? String(error.message) : String(error) }, bytes: new Uint8Array(0) }
    }
    const headers = []
    reply.headers.forEach((value, name) => { headers.push([name, value]) })
    const body = new Uint8Array(await reply.arrayBuffer())
    return { answer: { status: reply.status, headers, now: nowSeconds(), randomBase64: randomBase64(48) }, bytes: body }
  }

  let queue = Promise.resolve()

  /** One request, start to end. */
  async function serve (request) {
    const record = {
      method: request.method,
      target: request.target,
      headers: request.headers,
      now: nowSeconds(),
      randomBase64: randomBase64(16),
      remoteAddress: typeof request.remoteAddress === 'string' ? request.remoteAddress : ''
    }
    let got = blobCall(engine, 'webdavStep', [handle, JSON.stringify(record)], request.body || new Uint8Array(0))
    for (let hop = 0; hop < MAX_HOPS; hop += 1) {
      const env = got.envelope
      if (env.response !== undefined) {
        if (env.write !== undefined) replaceFile(configDir, env.write)
        return { status: env.response.status, headers: env.response.headers || [], body: got.bytes }
      }
      let answer
      let bytes
      if (env.lws !== undefined) {
        const storage = storages.get(env.lws.mount)
        if (storage === undefined) throw new WebdavHostError(`the engine named a storage that is not open: ${env.lws.mount}`)
        const req = env.lws.request
        const a = await storage.step({ method: req.method, target: req.target, headers: req.headers || [], body: got.bytes })
        answer = { status: a.status, headers: a.headers }
        bytes = a.body
      } else if (env.fetch !== undefined) {
        const x = await exchange(env.fetch, got.bytes)
        answer = x.answer
        bytes = x.bytes
      } else if (env.need !== undefined) {
        // A login: the one WebCrypto derivation the engine named.
        answer = await answerCipherRequest(env.need)
        bytes = new Uint8Array(0)
      } else {
        throw new WebdavHostError('the engine answered neither response, lws, fetch nor need')
      }
      got = blobCall(engine, 'webdavResume', [handle, JSON.stringify(answer)], bytes)
    }
    throw new WebdavHostError('a request took more engine answers than this host allows')
  }

  return {
    handle,
    engine,
    mounts: ready.mounts || [],
    warnings: ready.warnings || [],
    /** The start notices of the local mounts (a stale lock taken over,
     *  encryption at rest on or off), for standard error. */
    storageNotices,
    /**
     * One request, served after the requests before it.
     * @param {{method: string, target: string, headers: Array<[string, string]>, body: Uint8Array, remoteAddress?: string}} request
     */
    step (request) {
      const run = queue.then(() => serve(request))
      queue = run.catch(() => {})
      return run
    },
    close () {
      for (const s of storages.values()) s.close()
      try { engine.call('webdavClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** The addresses of this machine's interfaces. Pure I/O. */
async function interfaceAddresses () {
  try {
    const os = await import('node:os')
    return Object.values(os.networkInterfaces()).flat().filter(Boolean).map((i) => i.address)
  } catch (_error) {
    return []
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
  for (let index = 0; index + 1 < raw.length; index += 2) pairs.push([raw[index], raw[index + 1]])
  return pairs
}

function writeHeaders (response, pairs) {
  for (const pair of pairs) {
    if (!Array.isArray(pair) || pair.length < 2) continue
    const existing = response.getHeader(pair[0])
    if (existing === undefined) response.setHeader(pair[0], String(pair[1]))
    else if (Array.isArray(existing)) response.setHeader(pair[0], existing.concat([String(pair[1])]))
    else response.setHeader(pair[0], [String(existing), String(pair[1])])
  }
}

/**
 * Start the server: open the handle, then listen.
 *
 * @param {object} options `configDir`, `port` (default 8090), `host`
 *   (default 127.0.0.1), `engine`, `onError`, `users` (a users file),
 *   `cert` and `key` (PEM bytes: listen with TLS), `loginLimit`,
 *   `loginWindow`, `disableRateLimits` (the failed-login limit)
 * @returns {Promise<{server: object, port: number, origin: string, mounts: object[], close: Function}>}
 */
export async function listen (options = {}) {
  const tls = options.cert !== undefined && options.key !== undefined
  const http = tls ? await import('node:https') : await import('node:http')
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  const localGuard = {
    host,
    addresses: await interfaceAddresses(),
    ...(Array.isArray(options.allowHosts) ? { allowHosts: options.allowHosts } : {}),
    ...(Array.isArray(options.allowOrigins) ? { allowOrigins: options.allowOrigins } : {})
  }
  const dav = await openWebdav({ ...options, tls, host, localGuard })
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`webdav-serve: ${error.message}`) }
  const handler = async (request, response) => {
    let answer
    try {
      const body = await readBody(request)
      answer = await dav.step({
        method: request.method,
        target: request.url,
        headers: headerPairs(request.rawHeaders),
        body,
        remoteAddress: request.socket.remoteAddress
      })
    } catch (error) {
      onError(error)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end(`webdav-serve: ${error.message}\n`)
      return
    }
    writeHeaders(response, answer.headers)
    response.statusCode = answer.status
    response.end(answer.body)
  }
  const server = tls ? http.createServer({ cert: options.cert, key: options.key }, handler) : http.createServer(handler)
  const port = typeof options.port === 'number' ? options.port : 8090
  try {
    await new Promise((resolve, reject) => {
      server.once('error', reject)
      server.listen(port, host, resolve)
    })
  } catch (error) {
    dav.close()
    throw error
  }
  const bound = server.address()
  const origin = `${tls ? 'https' : 'http'}://${host.includes(':') ? `[${host}]` : host}:${bound.port}`
  return {
    server,
    port: bound.port,
    origin,
    mounts: dav.mounts,
    warnings: dav.warnings,
    storageNotices: dav.storageNotices,
    close () {
      return new Promise((resolve) => {
        server.close(() => { dav.close(); resolve() })
        if (typeof server.closeAllConnections === 'function') server.closeAllConnections()
      })
    }
  }
}
