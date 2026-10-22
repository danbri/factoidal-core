// A Node HTTP host for the authorization server component.
// https://github.com/danbri/factoidal/issues/916
// Design record: docs/designissues/2026-10-22-authorization-server.md
//
// WHAT THIS FILE IS ALLOWED TO DO
// Accept a socket, turn one HTTP request into the JSON request record,
// call the engine's `authzStep` on a handle, and write the JSON response
// record back. Read the clock, draw random bytes, resolve host names, fetch
// the documents the engine names, and read and write the key file. That is
// the whole contract (iron rule 7 of CLAUDE.md, anti-pattern 36).
//
// It makes NO protocol or token decision: no status code, no OAuth error
// code, no claim, no key choice, no address check. Every one of those lives
// in `formal/lean4/L4Factoidal/Authz/`. The one status code written here is
// 500, for a failure of this host itself.
//
// THE WASM CONTRACT (Wasm/Ops/Authz.lean)
//   authzOpen    [configJson]              -> { ok, handle, issuer, kid, changed }
//   authzStep    [handle, requestJson]     -> { ok, response, changed }
//                                            | { ok, resolve: { host }, changed }
//                                            | { ok, fetch: { url, accept, address }, changed }
//   authzFetched [handle, { url, status, body, now } | { host, addresses, now }] -> { ok }
//   authzKeys    [handle, { nonce?, private? }] -> { ok, keys } | { ok, jwks }
//   authzRotate  [handle, { now, random }]  -> { ok, changed, kid }
//   authzClose   [handle]                   -> { ok }
//
// FETCHES. `resolve` names a host: this host resolves it (`dns.lookup`, every
// address) and passes the addresses back; the engine decides whether they may
// be reached (loopback, link-local and private addresses are refused unless
// the configuration says `allowPrivateFetch`). `fetch` names a URL and the
// address to connect to: this host connects to exactly that address (the name
// is not resolved again), sends no cookie or credential, follows no redirect,
// reads at most MAX_DOCUMENT_BYTES, and passes the status and the text back.

import { closeSync, existsSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, writeSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { loadEngine } from '../bin/engine.mjs'
import { storageKeyText } from '../lws/persist.mjs'

/** The ops this host needs from the engine. */
export const AUTHZ_OPS = ['authzOpen', 'authzStep', 'authzFetched', 'authzKeys', 'authzRotate', 'authzClose']

/** The key file in DIR. */
export const KEY_FILE = 'authz-keys.json'

/** Bounds on what one request may make this host do. */
const MAX_NEEDS = 16
const FETCH_TIMEOUT_MS = 10000
const MAX_DOCUMENT_BYTES = 1048576

/** Random bytes for the engine, base64. Pure I/O. */
function randomBase64 (size) {
  const bytes = new Uint8Array(size)
  globalThis.crypto.getRandomValues(bytes)
  return Buffer.from(bytes).toString('base64')
}

function nowSeconds () {
  return Math.floor(Date.now() / 1000)
}

/** An error raised by this host, as opposed to one the engine reported. */
export class AuthzHostError extends Error {
  constructor (message) {
    super(message)
    this.name = 'AuthzHostError'
  }
}

/** Read the key file of DIR, or null. */
export function readKeyFile (dir) {
  const file = join(resolve(dir), KEY_FILE)
  if (!existsSync(file)) return null
  const text = readFileSync(file, 'utf8')
  try {
    return JSON.parse(text)
  } catch (error) {
    throw new AuthzHostError(`${file} is not JSON: ${error.message}`)
  }
}

/** Write the key file of DIR: temporary file, fsync, rename, mode 0600. */
export function writeKeyFile (dir, doc) {
  const root = resolve(dir)
  mkdirSync(root, { recursive: true })
  const file = join(root, KEY_FILE)
  const temporary = join(root, `.${KEY_FILE}.${process.pid}.tmp`)
  const fd = openSync(temporary, 'w', 0o600)
  try {
    writeSync(fd, JSON.stringify(doc))
    fsyncSync(fd)
  } finally {
    closeSync(fd)
  }
  renameSync(temporary, file)
  try {
    const dirFd = openSync(root, 'r')
    try { fsyncSync(dirFd) } finally { closeSync(dirFd) }
  } catch (_error) {
    // Some platforms cannot fsync a directory; the rename stands.
  }
}

/** Every address of a host name. Pure I/O. */
async function resolveHost (host) {
  try {
    const dns = await import('node:dns')
    const found = await dns.promises.lookup(host, { all: true, verbatim: true })
    return found.map((a) => a.address)
  } catch (_error) {
    return []
  }
}

/** GET one URL from the address the engine named. Pure I/O: status 0 and a
 *  message when there is no answer. */
async function fetchFrom (url, accept, address) {
  let target
  try {
    target = new URL(url)
  } catch (error) {
    return { status: 0, body: `not a URL: ${url}` }
  }
  const module = target.protocol === 'https:' ? await import('node:https') : await import('node:http')
  const family = address.indexOf(':') >= 0 ? 6 : 4
  return new Promise((done) => {
    const request = module.request(target, {
      method: 'GET',
      headers: { accept },
      lookup: (_host, options, callback) => {
        if (options && options.all) callback(null, [{ address, family }])
        else callback(null, address, family)
      },
      timeout: FETCH_TIMEOUT_MS
    }, (response) => {
      const chunks = []
      let size = 0
      response.on('data', (chunk) => {
        size += chunk.length
        if (size > MAX_DOCUMENT_BYTES) {
          response.destroy()
          done({ status: 0, body: `the document at ${url} is larger than ${MAX_DOCUMENT_BYTES} bytes` })
          return
        }
        chunks.push(chunk)
      })
      response.on('end', () => done({ status: response.statusCode, body: Buffer.concat(chunks).toString('utf8') }))
      response.on('error', (error) => done({ status: 0, body: String(error.message) }))
    })
    request.on('timeout', () => request.destroy(new Error('timeout')))
    request.on('error', (error) => done({ status: 0, body: String(error.message) }))
    request.end()
  })
}

/**
 * Open one authorization server on the engine.
 *
 * @param {object} options
 * @param {string} options.issuer the issuer identifier (http or https, no query)
 * @param {string[]} options.resources the resource IRIs tokens may be issued for
 * @param {string} [options.dir] the directory of the key file
 * @param {string} [options.alg] "ES256" (default) or "EdDSA"
 * @param {number} [options.tokenLifetime] seconds, 1 to 300 (default 300)
 * @param {number} [options.rotateAfter] seconds; 0 (default) never
 * @param {boolean} [options.allowHttp] accept http subjects (default false)
 * @param {boolean} [options.allowPrivateFetch] fetch from loopback, link-local and private addresses (default false)
 * @param {string|null} [options.storageKey] the key text; default FACTOIDAL_LWS_KEY; null reads none
 * @param {object} [options.engine] an engine to reuse
 */
export async function openAuthorizationServer (options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const dir = typeof options.dir === 'string' ? options.dir : null
  const config = {
    issuer: options.issuer,
    resources: Array.isArray(options.resources) ? options.resources : [],
    now: nowSeconds(),
    entropy: randomBase64(64)
  }
  for (const name of ['alg', 'tokenLifetime', 'leeway', 'rotateAfter', 'docTtl']) {
    if (options[name] !== undefined) config[name] = options[name]
  }
  if (options.allowHttp === true) config.allowHttp = true
  if (options.allowPrivateFetch === true) config.allowPrivateFetch = true
  const key = storageKeyText(options.storageKey)
  if (key !== undefined) config.storageKey = key
  if (dir !== null) {
    const keys = readKeyFile(dir)
    if (keys !== null) config.keys = keys
  }
  const opened = engine.call('authzOpen', [JSON.stringify(config)])
  const handle = opened.handle
  if (typeof handle !== 'string') throw new AuthzHostError('authzOpen answered with no handle')

  const persist = (envelope) => {
    if (dir === null || envelope === null || typeof envelope !== 'object' || envelope.changed !== true) return
    const told = engine.call('authzKeys', [handle, JSON.stringify({ nonce: randomBase64(12) })])
    writeKeyFile(dir, told.keys)
  }
  persist(opened)

  return {
    engine,
    handle,
    issuer: opened.issuer,
    /**
     * One request.
     * @param {{method: string, target: string, headers: Array<[string, string]>, body: string}} request
     * @returns {Promise<{status: number, headers: Array<[string, string]>, body: string}>}
     */
    async step (request) {
      let needs = 0
      for (;;) {
        const now = nowSeconds()
        const record = { ...request, now, random: randomBase64(112) }
        const envelope = engine.call('authzStep', [handle, JSON.stringify(record)])
        persist(envelope)
        if (envelope.response !== undefined && envelope.response !== null) {
          const r = envelope.response
          return { status: r.status, headers: Array.isArray(r.headers) ? r.headers : [], body: typeof r.body === 'string' ? r.body : '' }
        }
        needs += 1
        if (needs > MAX_NEEDS) throw new AuthzHostError('the engine asked for more than one request may fetch')
        if (envelope.resolve !== undefined && envelope.resolve !== null) {
          const host = String(envelope.resolve.host)
          const addresses = await resolveHost(host)
          engine.call('authzFetched', [handle, JSON.stringify({ host, addresses, now: nowSeconds() })])
        } else if (envelope.fetch !== undefined && envelope.fetch !== null) {
          const f = envelope.fetch
          const got = await fetchFrom(String(f.url), String(f.accept), String(f.address))
          engine.call('authzFetched', [handle, JSON.stringify({ url: f.url, status: got.status, body: got.body, now: nowSeconds() })])
        } else {
          throw new AuthzHostError('authzStep answered with no response, resolve or fetch')
        }
      }
    },
    /** Make a new signing key now (the old one stays published). Returns
     *  the engine's envelope unread. */
    rotate () {
      const told = engine.call('authzRotate', [handle, JSON.stringify({ now: nowSeconds(), random: randomBase64(64) })])
      persist(told)
      return told
    },
    /** The private JWKs of the published keys: for a test harness only. */
    privateJwks () {
      return engine.call('authzKeys', [handle, JSON.stringify({ private: true })]).jwks
    },
    close () {
      try { engine.call('authzClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

function headerPairs (raw) {
  const pairs = []
  for (let index = 0; index + 1 < raw.length; index += 2) pairs.push([raw[index], raw[index + 1]])
  return pairs
}

function readBody (request) {
  return new Promise((resolveBody, reject) => {
    const chunks = []
    request.on('data', (chunk) => chunks.push(chunk))
    request.on('error', reject)
    request.on('end', () => resolveBody(Buffer.concat(chunks).toString('utf8')))
  })
}

/**
 * Start an authorization server: listen, then open the engine handle. With
 * no `issuer` the issuer is the bound origin.
 *
 * @param {object} options as `openAuthorizationServer`, plus `port`, `host`
 * @returns {Promise<{server: object, port: number, origin: string, issuer: string,
 *                    authz: object, close: Function}>}
 */
export async function listen (options = {}) {
  const http = await import('node:http')
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  let authz = null
  const server = http.createServer(async (request, response) => {
    let answer
    try {
      const record = {
        method: request.method,
        target: request.url,
        headers: headerPairs(request.rawHeaders),
        body: await readBody(request)
      }
      answer = await authz.step(record)
    } catch (error) {
      console.error(`authz-serve: ${error && error.message ? error.message : error}`)
      response.writeHead(500, { 'content-type': 'text/plain' })
      response.end('authz-serve: host failure\n')
      return
    }
    for (const [name, value] of answer.headers) response.setHeader(name, String(value))
    response.statusCode = answer.status
    response.end(request.method === 'HEAD' ? undefined : answer.body)
  })
  await new Promise((resolveListen, reject) => {
    server.once('error', reject)
    server.listen(port, host, resolveListen)
  })
  const bound = server.address()
  const origin = `http://${host.indexOf(':') >= 0 ? `[${host}]` : host}:${bound.port}`
  try {
    authz = await openAuthorizationServer({ ...options, issuer: typeof options.issuer === 'string' ? options.issuer : origin })
  } catch (error) {
    await new Promise((resolveClose) => server.close(resolveClose))
    throw error
  }
  return {
    server,
    port: bound.port,
    origin,
    issuer: authz.issuer,
    authz,
    close () {
      return new Promise((resolveClose) => {
        server.close(() => { authz.close(); resolveClose() })
      })
    }
  }
}
