#!/usr/bin/env node
// An lws-driver/1 adapter for the Factoidal LWS client.
// https://github.com/danbri/factoidal/issues/917 (the client)
// https://github.com/danbri/factoidal/issues/1065 (the protocol reading moved into Lean)
// Protocol: lws-client driver/PROTOCOL.md (https://github.com/ebremer/lws-client)
//
//   node adapter.mjs
//   FACTOIDAL_CLIENT_MODULE=/opt/factoidal/lws/client.mjs node adapter.mjs
//
// WHAT THIS FILE IS ALLOWED TO DO (iron rule 7 of CLAUDE.md)
// It translates JSON. A protocol request becomes one call of the Factoidal
// client (npm `@factoidal/core/lws/client`, Lean
// formal/lean4/L4Factoidal/LWS/Client/), and the `report` member of the
// client's answer is the protocol's result. Every decision about the wire is
// the client's: which request is sent, its headers, its media types, the
// authorization flow, retries, paging. Every reading of a response is the
// client's too: the result shapes (Metadata, Item, Page, Storage,
// Subscription), the name of an error, the media type of a linkset, the type
// of an ID token, the did:key of a new key. This file builds no URL, sends no
// request of its own, reads no header, keeps no map of what it has seen and
// retries nothing.
//
// The only things it does besides renaming members are the driver's own
// conventions: the `limit` of a lazy sequence, the form of a request body
// (text, base64 or json), and the check that an argument has the JSON type
// the protocol names.

import { createInterface } from 'node:readline'
import { readFileSync } from 'node:fs'
import { pathToFileURL, fileURLToPath } from 'node:url'
import { dirname, join, isAbsolute, resolve as resolvePath } from 'node:path'

// ---------------------------------------------------------------------------
// The client module

function clientModuleUrl () {
  const named = process.env.FACTOIDAL_CLIENT_MODULE
  if (named === undefined || named === '') return new URL('../../npm/factoidal/lws/client.mjs', import.meta.url)
  if (/^file:/i.test(named)) return new URL(named)
  return pathToFileURL(isAbsolute(named) ? named : resolvePath(process.cwd(), named))
}

const moduleUrl = clientModuleUrl()
const { createLwsClient, createDidKey, LwsClientError } = await import(moduleUrl.href)

function packageVersion () {
  try {
    const dir = dirname(fileURLToPath(moduleUrl))
    return JSON.parse(readFileSync(join(dir, '..', 'package.json'), 'utf8')).version
  } catch {
    return 'unknown'
  }
}

const LIBRARY = `factoidal-lws-client/${packageVersion()}`

/** A failure of this file: an argument, or a feature the client lacks. */
class AdapterError extends Error {
  constructor (kind, message) {
    super(message)
    this.kind = kind
  }
}
/** An error the client already named (its `report`). */
class Reported extends Error {
  constructor (report) {
    super(report.message)
    this.report = report
  }
}
const invalid = (message) => new AdapterError('InvalidArguments', message)
const unsupported = (message) => new AdapterError('Unsupported', message)

// ---------------------------------------------------------------------------
// Arguments

function typeOk (value, type) {
  if (type === 'array') return Array.isArray(value)
  if (type === 'object') return value !== null && typeof value === 'object' && !Array.isArray(value)
  return typeof value === type
}

function required (args, name, type = 'string') {
  const value = args[name]
  if (value === undefined || value === null) throw invalid(`missing argument '${name}'`)
  if (!typeOk(value, type)) throw invalid(`argument '${name}' must be a ${type}`)
  return value
}

function optional (args, name, type = 'string') {
  const value = args[name]
  if (value === undefined || value === null) return undefined
  if (!typeOk(value, type)) throw invalid(`argument '${name}' must be a ${type}`)
  return value
}

/** A non-negative integer argument. */
function natural (args, name) {
  const value = optional(args, name, 'number')
  if (value !== undefined && !(Number.isInteger(value) && value >= 0)) throw invalid(`argument '${name}' must be a non-negative integer`)
  return value
}

/** A request target: an absolute URL. */
function targetOf (args, name) {
  const url = required(args, name)
  let parsed
  try {
    parsed = new URL(url)
  } catch {
    throw invalid(`argument '${name}' must be an absolute URL`)
  }
  if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') throw invalid(`argument '${name}' must be an http or https URL`)
  return url
}

function base64Bytes (text, name) {
  if (!/^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/.test(text)) throw invalid(`argument '${name}' is not base64`)
  return new Uint8Array(Buffer.from(text, 'base64'))
}

/** A protocol `body` as bytes and the content type it implies (PROTOCOL.md section 3). */
function bodyOf (body, contentType) {
  if (body === undefined || body === null) return { bytes: undefined, contentType }
  if (typeof body !== 'object') throw invalid("argument 'body' must be an object")
  if (typeof body.text === 'string') return { bytes: new TextEncoder().encode(body.text), contentType }
  if (typeof body.base64 === 'string') return { bytes: base64Bytes(body.base64, 'body.base64'), contentType }
  if ('json' in body) return { bytes: new TextEncoder().encode(JSON.stringify(body.json)), contentType: contentType ?? 'application/json' }
  throw invalid("argument 'body' must have text, base64 or json")
}

/** The `limit` of a lazy sequence, and the cut it makes. */
function limited (items, args) {
  const limit = natural(args, 'limit') ?? 1000
  return { items: items.slice(0, limit), truncated: items.length > limit }
}

/** The client checks the operations of a patch; the array goes to it as it is. */
function patchBody (patch) {
  if (!Array.isArray(patch)) throw invalid("argument 'patch' must be an array of operations")
  return new TextEncoder().encode(JSON.stringify(patch))
}

/** A write's precondition, in the names of the client's `precondition` member. */
function preconditionOf (args) {
  const ifMatch = optional(args, 'ifMatch')
  const ifNoneMatch = optional(args, 'ifNoneMatch')
  if (ifMatch !== undefined && ifNoneMatch !== undefined) throw unsupported('ifMatch and ifNoneMatch together')
  if (ifMatch !== undefined) return { precondition: 'ifMatch', tag: ifMatch }
  if (ifNoneMatch !== undefined) {
    if (ifNoneMatch === '*') return { precondition: 'ifNoneMatchStar' }
    throw unsupported('ifNoneMatch other than "*" on a write')
  }
  return {}
}

// ---------------------------------------------------------------------------
// Errors: the client names them

function errorResult (e) {
  if (e instanceof AdapterError) return { kind: e.kind, message: e.message }
  if (e instanceof Reported) return e.report
  if ((e instanceof LwsClientError || e?.name === 'LwsClientError') && e.report !== undefined) return e.report
  return { kind: 'InternalError', message: e?.stack ?? String(e) }
}

// ---------------------------------------------------------------------------
// The client

let client = null
let configured = { userAgent: undefined, timeoutSeconds: undefined, headers: undefined, options: { legacyChallenge: true } }

/** A `fetch` that adds only what `configure` asked for: a user agent, extra
 *  headers, a timeout. The request is otherwise the client's. */
function wireFetch () {
  const { userAgent, timeoutSeconds, headers } = configured
  return async (url, init = {}) => {
    const h = new Headers(init.headers ?? [])
    for (const [name, value] of Object.entries(headers ?? {})) h.set(name, String(value))
    if (userAgent !== undefined) h.set('user-agent', userAgent)
    const next = { ...init, headers: h }
    if (timeoutSeconds !== undefined) next.signal = AbortSignal.timeout(timeoutSeconds * 1000)
    return fetch(url, next)
  }
}

async function theClient () {
  if (client === null) client = await createLwsClient({ fetch: wireFetch(), ...configured.options })
  return client
}

async function configure (args) {
  const auth = args.auth ?? { type: 'none' }
  if (auth === null || typeof auth !== 'object' || Array.isArray(auth)) throw invalid("argument 'auth' must be an object")
  // The driver protocol has no option for the challenge of the drafts before
  // 2026-10-19; its Java and JS clients follow it always, so this client does
  // too (https://github.com/danbri/factoidal/issues/1115).
  const next = { userAgent: optional(args, 'userAgent'), timeoutSeconds: optional(args, 'timeoutSeconds', 'number'), headers: optional(args, 'headers', 'object'), options: { legacyChallenge: true } }
  if (next.timeoutSeconds !== undefined && !(Number.isInteger(next.timeoutSeconds) && next.timeoutSeconds > 0)) throw invalid("argument 'timeoutSeconds' must be a positive integer")
  if (optional(args, 'allowInsecureHttp', 'boolean') === false) throw unsupported('allowInsecureHttp false: the client does not refuse http')
  const result = { library: LIBRARY }
  switch (auth.type) {
    case 'none':
      break
    case 'bearer': {
      const bearer = { token: required(auth, 'token') }
      const realm = optional(auth, 'realm')
      if (realm !== undefined) bearer.realm = realm
      next.options.bearer = bearer
      break
    }
    case 'openid':
      next.options.idToken = required(auth, 'idToken')
      break
    case 'selfSigned': {
      const agent = required(auth, 'agent')
      const jwk = required(auth, 'privateJwk', 'object')
      const kid = optional(auth, 'kid') ?? jwk.kid
      if (typeof kid !== 'string') throw invalid("selfSigned needs 'kid', or a 'kid' in the private JWK")
      next.options.selfIssued = { subject: agent, keyId: kid, jwk }
      result.agent = agent
      result.kid = kid
      break
    }
    case 'didKey': {
      const key = await createDidKey({ algorithm: optional(auth, 'algorithm') ?? 'ES256' })
      next.options.selfIssued = key.selfIssued
      result.agent = key.agent
      result.kid = key.kid
      break
    }
    default:
      throw invalid(`unknown auth type '${auth.type}'`)
  }
  configured = next
  client = null
  await theClient()
  return result
}

// ---------------------------------------------------------------------------
// Operations

/** One client operation; its answer. */
async function run (kind, url, extra = {}) {
  return (await theClient()).run({ ...extra, kind, url })
}

/** One client operation; the result the protocol names. */
async function report (kind, url, extra = {}) {
  return (await run(kind, url, extra)).report
}

/** A listing, cut at `limit`. */
async function listing (kind, url, args, extra = {}) {
  const found = (await report(kind, url, extra)).items
  return limited(found, args)
}

/** The members of an access document are the client's arguments: one policy. */
async function accessWrite (kind, args, doc, type) {
  const serviceUrl = targetOf(args, 'serviceUrl')
  const policies = [].concat(doc.access ?? [])
  if (policies.length !== 1) throw unsupported(`${type} with ${policies.length} policies: the client writes one policy`)
  const policy = policies[0]
  const target = policy.target
  const targets = [].concat(target?.value ?? target ?? []).filter((t) => typeof t === 'string')
  const extra = { actions: [].concat(policy.action ?? []), assignee: policy.assignee, targets }
  if (policy.constraint !== undefined) extra.constraint = policy.constraint
  if (typeof doc.inbox === 'string') extra.inbox = doc.inbox
  return report(kind, serviceUrl, extra)
}

const operations = {
  configure,

  async discover_storage (args) {
    return report('discover', targetOf(args, 'url'))
  },

  async get_storage_description (args) {
    return report('describe', targetOf(args, 'url'))
  },

  async head (args) {
    return report('head', targetOf(args, 'url'))
  },

  async read (args) {
    const extra = {}
    for (const name of ['accept', 'ifNoneMatch', 'prefer']) {
      const value = optional(args, name)
      if (value !== undefined) extra[name] = value
    }
    for (const name of ['rangeStart', 'rangeEnd']) {
      const value = natural(args, name)
      if (value !== undefined) extra[name] = value
    }
    return report('read', targetOf(args, 'url'), extra)
  },

  async read_container (args) {
    return report('readPage', targetOf(args, 'url'))
  },

  async list_container (args) {
    return listing('list', targetOf(args, 'url'), args)
  },

  async create (args) {
    const container = targetOf(args, 'container')
    const { bytes, contentType } = bodyOf(args.body, optional(args, 'contentType'))
    const extra = {}
    if (bytes !== undefined) extra.body = bytes
    if (contentType !== undefined) extra.mediaType = contentType
    const slug = optional(args, 'slug')
    if (slug !== undefined) extra.slug = slug
    const types = optional(args, 'types', 'array')
    if (types !== undefined) extra.types = types
    const links = optional(args, 'links', 'array')
    if (links !== undefined) extra.linkObjects = links
    return report('create', container, extra)
  },

  async create_container (args) {
    const extra = { container: true }
    const slug = optional(args, 'slug')
    if (slug !== undefined) extra.slug = slug
    return report('create', targetOf(args, 'parent'), extra)
  },

  async update (args) {
    const url = targetOf(args, 'url')
    if (args.body === undefined || args.body === null) throw invalid("missing argument 'body'")
    const { bytes, contentType } = bodyOf(args.body, optional(args, 'contentType'))
    const extra = { body: bytes, ...preconditionOf(args) }
    if (contentType !== undefined) extra.mediaType = contentType
    return report('update', url, extra)
  },

  async patch (args) {
    const url = targetOf(args, 'url')
    if (args.ifNoneMatch !== undefined && args.ifNoneMatch !== null) throw unsupported('ifNoneMatch on patch')
    return report('patch', url, { body: patchBody(args.patch), ...preconditionOf(args) })
  },

  async delete (args) {
    const extra = { ...preconditionOf(args) }
    if (optional(args, 'recursive', 'boolean')) extra.recursive = true
    await run('delete', targetOf(args, 'url'), extra)
    return {}
  },

  async linkset_url (args) {
    return report('findLinkset', targetOf(args, 'url'))
  },

  async read_linkset (args) {
    return report('readLinkset', targetOf(args, 'url'))
  },

  async update_linkset (args) {
    const linksetUrl = targetOf(args, 'linksetUrl')
    const doc = required(args, 'linkset', 'object')
    const extra = { linksetUrl, body: new TextEncoder().encode(JSON.stringify(doc)), ...preconditionOf({ ifMatch: args.ifMatch }) }
    return report('putLinkset', linksetUrl, extra)
  },

  async patch_linkset (args) {
    const linksetUrl = targetOf(args, 'linksetUrl')
    const extra = { linksetUrl, body: patchBody(args.patch), ...preconditionOf({ ifMatch: args.ifMatch }) }
    return report('updateLinkset', linksetUrl, extra)
  },

  async move (args) {
    const extra = { destination: targetOf(args, 'destination'), ...preconditionOf({ ifMatch: args.ifMatch }) }
    return report('move', targetOf(args, 'url'), extra)
  },

  async subscribe (args) {
    // `serviceUrl` is the notification service endpoint: the client POSTs to
    // it with no discovery, as the driver's other clients do.
    const serviceUrl = targetOf(args, 'serviceUrl')
    const extra = { topics: required(args, 'topics', 'array'), inbox: required(args, 'inbox'), endpoint: serviceUrl }
    const expires = optional(args, 'expires')
    if (expires !== undefined) extra.expires = expires
    return report('subscribe', serviceUrl, extra)
  },

  async list_subscriptions (args) {
    return listing('list', targetOf(args, 'serviceUrl'), args)
  },

  async get_subscription (args) {
    return report('getSubscription', targetOf(args, 'url'))
  },

  async unsubscribe (args) {
    await run('unsubscribe', targetOf(args, 'url'))
    return {}
  },

  async verify_notification (args) {
    const url = targetOf(args, 'url')
    const headers = required(args, 'headers', 'object')
    const extra = { method: required(args, 'method'), body: base64Bytes(required(args, 'bodyBase64'), 'bodyBase64') }
    const trusted = optional(args, 'trustedStorages', 'array')
    if (trusted !== undefined) extra.trustedStorages = trusted
    extra.headers = []
    for (const [name, value] of Object.entries(headers)) for (const v of [].concat(value)) extra.headers.push([name, String(v)])
    const done = await run('verifyNotification', url, extra)
    if (done.accept !== true) throw new Reported(done.report)
    return done.report
  },

  async request_access (args) {
    return { location: (await accessWrite('requestAccess', args, required(args, 'request', 'object'), 'AccessRequest')).location }
  },

  async get_access_request (args) {
    return report('getAccess', targetOf(args, 'url'))
  },

  async list_access_requests (args) {
    return listing('list', targetOf(args, 'serviceUrl'), args)
  },

  async cancel_access_request (args) {
    await run('delete', targetOf(args, 'url'))
    return {}
  },

  async grant_access (args) {
    return { location: (await accessWrite('grantAccess', args, required(args, 'grant', 'object'), 'AccessGrant')).location }
  },

  async get_access_grant (args) {
    return report('getAccess', targetOf(args, 'url'))
  },

  async list_access_grants (args) {
    return listing('list', targetOf(args, 'serviceUrl'), args)
  },

  async revoke_access_grant (args) {
    await run('revokeAccess', targetOf(args, 'url'))
    return {}
  },

  async read_type_index (args) {
    const endpoint = targetOf(args, 'url')
    return report('typeIndex', endpoint, { endpoint, onePage: true })
  },

  async list_types (args) {
    const endpoint = targetOf(args, 'serviceUrl')
    const found = (await report('typeIndex', endpoint, { endpoint })).types
    const { items, truncated } = limited(found, args)
    return { types: items, truncated }
  },

  async search_types (args) {
    const endpoint = targetOf(args, 'serviceUrl')
    return report('search', endpoint, { endpoint, query: required(args, 'query', 'object'), onePage: true })
  },

  async search_all (args) {
    const endpoint = targetOf(args, 'serviceUrl')
    return listing('search', endpoint, args, { endpoint, query: required(args, 'query', 'object') })
  },

  async accepted_query_formats (args) {
    return report('queryFormats', targetOf(args, 'serviceUrl'))
  },

  async shutdown () {
    return {}
  }
}

// ---------------------------------------------------------------------------
// The protocol loop

function write (message) {
  process.stdout.write(`${JSON.stringify(message)}\n`)
}

// stdout carries protocol messages only.
console.log = console.info = console.debug = (...args) => console.error(...args)

write({
  hello: {
    protocol: 'lws-driver/1', language: 'factoidal', library: LIBRARY,
    operations: Object.keys(operations)
  }
})

const lines = createInterface({ input: process.stdin, crlfDelay: Infinity })
for await (const line of lines) {
  if (line.trim() === '') continue
  let request
  try {
    request = JSON.parse(line)
  } catch {
    write({ id: null, ok: false, error: { kind: 'InvalidArguments', message: 'the request is not JSON' } })
    continue
  }
  if (request === null || typeof request !== 'object' || Array.isArray(request)) {
    write({ id: null, ok: false, error: { kind: 'InvalidArguments', message: 'the request is not a JSON object' } })
    continue
  }
  const { id, op } = request
  const args = request.args ?? {}
  const operation = Object.hasOwn(operations, op) ? operations[op] : undefined
  if (!operation) {
    write({ id, ok: false, error: { kind: 'Unsupported', message: `unknown operation '${op}'` } })
    continue
  }
  try {
    if (args === null || typeof args !== 'object' || Array.isArray(args)) throw invalid('args must be an object')
    write({ id, ok: true, result: await operation(args) })
  } catch (e) {
    write({ id, ok: false, error: errorResult(e) })
  }
  if (op === 'shutdown') break
}
process.exit(0)
