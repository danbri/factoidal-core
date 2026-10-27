#!/usr/bin/env node
// An lws-driver/1 adapter for the Factoidal LWS client.
// https://github.com/danbri/factoidal/issues/917 (the client)
// Protocol: lws-client driver/PROTOCOL.md (https://github.com/ebremer/lws-client)
//
//   node adapter.mjs
//   FACTOIDAL_CLIENT_MODULE=/opt/factoidal/lws/client.mjs node adapter.mjs
//
// WHAT THIS FILE IS ALLOWED TO DO (iron rule 7 of CLAUDE.md)
// It is a host. It turns a protocol request into one call of the Factoidal
// client (npm `@factoidal/core/lws/client`, Lean
// formal/lean4/L4Factoidal/LWS/Client/) and turns the client's answer into the
// protocol's result shape. Every decision about the wire is the client's:
// which request is sent, its headers, its media types, the authorization
// flow, retries, paging. This file builds no URL, sends no request of its own
// and retries nothing.
//
// Three things in this file are not a pure pass-through. Each is marked in
// the text and listed in README.md:
//   REPORTING   The protocol's result shapes (Metadata, Storage, Item) are
//               keyed by Link relations and by members of the storage
//               description. The client returns status, header pairs and the
//               body. This file reads them to fill those shapes. Nothing it
//               reads goes into a request.
//   KEY SETUP   `configure` with `didKey` makes a key pair and a did:key with
//               node:crypto. The client signs with it (the engine, HACL*).
//   ERROR NAMES `error.kind` is the protocol's name for an HTTP status.
//
// An operation or option the client does not have answers `Unsupported`, and
// the operation is left out of `hello.operations` when no use of it works.

import { createInterface } from 'node:readline'
import { readFileSync } from 'node:fs'
import { generateKeyPairSync } from 'node:crypto'
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
const { createLwsClient, LwsClientError } = await import(moduleUrl.href)

function packageVersion () {
  try {
    const dir = dirname(fileURLToPath(moduleUrl))
    return JSON.parse(readFileSync(join(dir, '..', 'package.json'), 'utf8')).version
  } catch {
    return 'unknown'
  }
}

const LIBRARY = `factoidal-lws-client/${packageVersion()}`

class AdapterError extends Error {
  constructor (kind, message) {
    super(message)
    this.kind = kind
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

/** A request target: an absolute http or https URL. */
function targetOf (args, name) {
  const url = required(args, name)
  if (!/^https?:\/\/[^/\s]/i.test(url) || !URL.canParse(url)) throw invalid(`argument '${name}' must be an absolute URL`)
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

function limitOf (args) {
  const limit = optional(args, 'limit', 'number') ?? 1000
  if (!Number.isInteger(limit) || limit < 0) throw invalid("argument 'limit' must be a non-negative integer")
  return limit
}

const PATCH_OPERATIONS = ['add', 'remove', 'replace', 'move', 'copy', 'test']

/** The RFC 6902 array is sent as it is: the client chooses the media type. */
function patchBody (patch) {
  if (!Array.isArray(patch)) throw invalid("argument 'patch' must be an array of operations")
  for (const op of patch) {
    if (op === null || typeof op !== 'object' || !PATCH_OPERATIONS.includes(op.op)) throw invalid('a patch operation must be an object with a known op')
  }
  return new TextEncoder().encode(JSON.stringify(patch))
}

/** The `application/lws-query+json` document goes to the client as it is. */
function queryOf (query) {
  if (query === null || typeof query !== 'object' || Array.isArray(query)) throw invalid("argument 'query' must be an object")
  for (const [key, groups] of Object.entries(query)) {
    if (!Array.isArray(groups)) throw invalid(`query member '${key}' must be a list of groups`)
    for (const group of groups) {
      const ok = typeof group === 'string' || (Array.isArray(group) && group.every((x) => typeof x === 'string'))
      if (!ok) throw invalid(`a group of query member '${key}' must be an IRI or a list of IRIs`)
    }
  }
  return query
}

/** A write's precondition, as the client names it. */
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
// REPORTING: the client's answer in the protocol's shapes
//
// The client answers `{ status, headers: [[name, value]], body | bodyBase64, ... }`.
// Nothing below feeds a request.

const REL_TYPE = 'type'
const REL_UP = 'up'
const REL_LINKSET = 'linkset'
const REL_STORAGE = 'https://www.w3.org/ns/lws#storage'

function headerMap (pairs) {
  const map = new Map()
  for (const [name, value] of Array.isArray(pairs) ? pairs : []) {
    const key = String(name).toLowerCase()
    map.set(key, map.has(key) ? `${map.get(key)}, ${value}` : String(value))
  }
  return map
}

function absolute (base, ref) {
  if (typeof ref !== 'string') return ref
  if (/^[a-z][a-z0-9+.-]*:/i.test(ref)) return ref
  try { return new URL(ref, base).href } catch { return ref }
}

/** RFC 8288 section 3 Link field value: the links, one per relation type. */
function parseLinks (value, base) {
  const links = []
  if (!value) return links
  let i = 0
  const n = value.length
  while (i < n) {
    while (i < n && /[\s,]/.test(value[i])) i += 1
    if (i >= n) break
    if (value[i] !== '<') { while (i < n && value[i] !== ',') i += 1; continue }
    const close = value.indexOf('>', i)
    if (close < 0) break
    const href = value.slice(i + 1, close)
    i = close + 1
    const params = {}
    while (i < n) {
      while (i < n && /\s/.test(value[i])) i += 1
      if (value[i] !== ';') break
      i += 1
      while (i < n && /\s/.test(value[i])) i += 1
      const start = i
      while (i < n && !/[=;,\s]/.test(value[i])) i += 1
      const name = value.slice(start, i).toLowerCase()
      let val = ''
      while (i < n && /\s/.test(value[i])) i += 1
      if (value[i] === '=') {
        i += 1
        while (i < n && /\s/.test(value[i])) i += 1
        if (value[i] === '"') {
          i += 1
          while (i < n && value[i] !== '"') { if (value[i] === '\\') i += 1; val += value[i] ?? ''; i += 1 }
          i += 1
        } else {
          const s = i
          while (i < n && !/[;,]/.test(value[i])) i += 1
          val = value.slice(s, i).trim()
        }
      }
      if (name) params[name] = val
    }
    const { rel, ...rest } = params
    for (const r of (rel ?? '').split(/\s+/).filter(Boolean)) links.push({ href: absolute(base, href), rel: r, params: rest })
  }
  return links
}

const splitList = (value) => (value ? value.split(',').map((s) => s.trim()).filter(Boolean) : [])

/** Metadata (PROTOCOL.md 3.1) from a response's status and header pairs. */
function metadataOf (url, status, headerPairs) {
  const h = headerMap(headerPairs)
  const links = parseLinks(h.get('link'), url)
  const first = (rel) => links.find((l) => l.rel === rel)?.href
  const length = h.get('content-length')
  return {
    url,
    status,
    etag: h.get('etag'),
    lastModified: h.get('last-modified'),
    contentType: h.get('content-type'),
    contentLength: length !== undefined && /^\d+$/.test(length) ? Number(length) : undefined,
    links,
    linkset: first(REL_LINKSET),
    parent: first(REL_UP),
    storage: first(REL_STORAGE),
    types: links.filter((l) => l.rel === REL_TYPE).map((l) => l.href),
    allow: splitList(h.get('allow')),
    acceptPatch: splitList(h.get('accept-patch'))
  }
}

// What the adapter has been told, kept to choose which URL it hands the client:
// the resource a linkset URL belongs to, and a URL inside each origin's storage.
const linksetOwners = new Map()
const storageUrls = new Map()

function remember (url, linkset) {
  try { storageUrls.set(new URL(url).origin, url) } catch { /* not a URL */ }
  if (typeof linkset === 'string') linksetOwners.set(linkset, url)
}

function metadataFrom (url, done) {
  const m = metadataOf(url, done.status, done.headers)
  if (done.status >= 200 && done.status < 300) remember(url, m.linkset)
  return m
}

/** A URL inside the storage of `serviceUrl`, which the client's index and search
 *  operations take (a service endpoint does not answer with the storage link). */
function insideStorage (serviceUrl) {
  return storageUrls.get(new URL(serviceUrl).origin) ?? serviceUrl
}

const TEXTUAL = /^(text\/[^;]*|application\/(json|xml)|[^;]*\+(json|xml))\s*(;|$)/i

/** The body bytes of a client answer. */
function bytesOfDone (done) {
  if (typeof done.bodyBase64 === 'string') return new Uint8Array(Buffer.from(done.bodyBase64, 'base64'))
  if (typeof done.body === 'string') return new TextEncoder().encode(done.body)
  return new Uint8Array(0)
}

function bodyResult (bytes, contentType) {
  if (contentType && TEXTUAL.test(contentType.trim())) return { text: new TextDecoder().decode(bytes) }
  return { base64: Buffer.from(bytes).toString('base64') }
}

function jsonOfDone (done) {
  try { return JSON.parse(new TextDecoder().decode(bytesOfDone(done))) } catch { return undefined }
}

const asList = (v) => (v === undefined || v === null ? [] : [].concat(v))

function itemOf (member, base) {
  if (typeof member === 'string') return { id: absolute(base, member), types: [] }
  return {
    id: absolute(base, member.id),
    types: asList(member.type),
    format: member.format,
    size: member.size,
    modified: member.modified
  }
}

const hasSuffix = (types, term) => types.some((t) => t === term || t.endsWith(`#${term}`) || t.endsWith(`:${term}`))

function storageOf (desc) {
  const services = asList(desc.service)
  const root = services.find((sv) => hasSuffix(asList(sv.type), 'StorageRoot'))
  const move = asList(desc.capability).find((c) => hasSuffix(asList(c.type), 'MoveResource'))
  const result = {
    id: desc.id,
    types: asList(desc.type),
    storageRoot: root?.serviceEndpoint,
    services: services.map((sv) => ({
      id: sv.id,
      types: asList(sv.type),
      serviceEndpoint: sv.serviceEndpoint,
      subscriptionType: sv.subscriptionType === undefined ? undefined : asList(sv.subscriptionType)
    })),
    verificationMethods: asList(desc.verificationMethod).map((vm) => ({ id: vm.id, type: vm.type, controller: vm.controller })),
    raw: desc
  }
  if (move) result.moveCapability = { appliesTo: move.appliesTo === undefined ? ['DataResource'] : asList(move.appliesTo), preservesIdentifier: move.preservesIdentifier }
  return result
}

function subscriptionOf (url, done) {
  const raw = jsonOfDone(done) ?? {}
  return { subscription: raw.id ? absolute(url, raw.id) : url, types: asList(raw.type), expires: raw.expires, raw }
}

// ---------------------------------------------------------------------------
// ERROR NAMES

const STATUS_KINDS = {
  400: 'BadRequestError', 401: 'UnauthorizedError', 403: 'ForbiddenError', 404: 'NotFoundError',
  405: 'MethodNotAllowedError', 406: 'NotAcceptableError', 409: 'ConflictError', 410: 'GoneError',
  412: 'PreconditionFailedError', 415: 'UnsupportedMediaTypeError', 422: 'UnprocessableContentError',
  501: 'NotImplementedError', 507: 'InsufficientStorageError'
}

const AUTHENTICATION_CODES = new Set(['authorization', 'discoveryValidation', 'credential'])
const PROTOCOL_CODES = new Set([
  'malformedDescription', 'malformedLinkset', 'malformedListing', 'noEtag', 'noLinkset', 'noMoveCapability',
  'noService', 'noStorageLink', 'noSubscriptionType', 'notAdvertised', 'methodRefused'
])

function errorOfFail (e) {
  const detail = e.detail ?? {}
  const status = typeof detail.status === 'number' ? detail.status : undefined
  const message = `${e.reason}${status !== undefined ? ` (status ${status})` : ''}: ${JSON.stringify(detail).slice(0, 600)}`
  if (e.reason === 'badArguments') return { kind: 'InvalidArguments', message }
  if (e.reason === 'transport') return { kind: 'TransportError', message }
  if (AUTHENTICATION_CODES.has(e.reason)) {
    const error = { kind: 'AuthenticationError', message }
    if (status !== undefined) error.status = status
    if (typeof detail.error === 'string') error.oauthError = detail.error
    if (typeof detail.errorDescription === 'string') error.oauthErrorDescription = detail.errorDescription
    return error
  }
  if (status !== undefined) {
    const error = { kind: STATUS_KINDS[status] ?? 'HttpError', status, message }
    const h = headerMap(detail.headers)
    const body = typeof detail.body === 'string' ? detail.body : undefined
    if (body !== undefined && /json/i.test(h.get('content-type') ?? '')) {
      try { error.problem = JSON.parse(body) } catch { /* not a problem document */ }
    }
    if (status === 405) error.allow = splitList(h.get('allow'))
    if (status === 415) error.acceptPatch = splitList(h.get('accept-patch'))
    return error
  }
  if (PROTOCOL_CODES.has(e.reason)) return { kind: 'ProtocolError', message }
  return { kind: 'InternalError', message }
}

function errorResult (e) {
  if (e instanceof AdapterError) return { kind: e.kind, message: e.message }
  if (e instanceof LwsClientError || e?.name === 'LwsClientError') return errorOfFail(e)
  return { kind: 'InternalError', message: e?.stack ?? String(e) }
}

// ---------------------------------------------------------------------------
// The client

let client = null
let configured = { userAgent: undefined, timeoutSeconds: undefined, headers: undefined, session: undefined, selfIssued: undefined, subjectToken: undefined, subjectTokenType: undefined }

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
  if (client === null) client = await createLwsClient({ fetch: wireFetch(), ...sessionOptions() })
  return client
}

function sessionOptions () {
  const o = {}
  if (configured.session !== undefined) o.session = configured.session
  if (configured.selfIssued !== undefined) o.selfIssued = configured.selfIssued
  if (configured.subjectToken !== undefined) { o.subjectToken = configured.subjectToken; o.subjectTokenType = configured.subjectTokenType }
  return o
}

// ---------------------------------------------------------------------------
// KEY SETUP (configure didKey)

const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
function base58 (bytes) {
  let n = 0n
  for (const b of bytes) n = n * 256n + BigInt(b)
  let out = ''
  while (n > 0n) { out = B58[Number(n % 58n)] + out; n /= 58n }
  for (const b of bytes) { if (b === 0) out = `1${out}`; else break }
  return out
}

/** did:key of a P-256 key (multicodec 0x1200, compressed point). */
function didKeyP256 (jwk) {
  const x = Buffer.from(jwk.x, 'base64url')
  const y = Buffer.from(jwk.y, 'base64url')
  const point = Buffer.concat([Buffer.from([(y[y.length - 1] & 1) === 1 ? 3 : 2]), x])
  return `did:key:z${base58(Buffer.concat([Buffer.from([0x80, 0x24]), point]))}`
}

const ID_TOKEN_TYPE = 'urn:ietf:params:oauth:token-type:id_token'

async function configure (args) {
  const auth = args.auth ?? { type: 'none' }
  if (auth === null || typeof auth !== 'object' || Array.isArray(auth)) throw invalid("argument 'auth' must be an object")
  const next = { userAgent: optional(args, 'userAgent'), timeoutSeconds: optional(args, 'timeoutSeconds', 'number'), headers: optional(args, 'headers', 'object') }
  if (next.timeoutSeconds !== undefined && !(Number.isInteger(next.timeoutSeconds) && next.timeoutSeconds > 0)) throw invalid("argument 'timeoutSeconds' must be a positive integer")
  if (optional(args, 'allowInsecureHttp', 'boolean') === false) throw unsupported('allowInsecureHttp false: the client does not refuse http')
  const result = { library: LIBRARY }
  switch (auth.type) {
    case 'none':
      break
    case 'bearer': {
      const token = required(auth, 'token')
      const realm = optional(auth, 'realm')
      if (realm === undefined) throw unsupported('bearer without a realm: the client sends a token only to URLs under a storage root')
      next.session = { tokens: [{ storage: realm, root: realm, token }] }
      break
    }
    case 'openid':
      // The protocol passes an ID Token the caller already has. The client has no sign-in
      // of its own (https://github.com/danbri/factoidal/issues/1043).
      next.subjectToken = required(auth, 'idToken')
      next.subjectTokenType = ID_TOKEN_TYPE
      break
    case 'selfSigned': {
      const agent = required(auth, 'agent')
      const jwk = required(auth, 'privateJwk', 'object')
      const kid = optional(auth, 'kid') ?? jwk.kid
      if (typeof kid !== 'string') throw invalid("selfSigned needs 'kid', or a 'kid' in the private JWK")
      if (jwk.kty !== 'EC' || jwk.crv !== 'P-256') throw unsupported('selfSigned with a key other than EC P-256: the client signs ES256 only')
      next.selfIssued = { subject: agent, keyId: kid, jwk }
      result.agent = agent
      result.kid = kid
      break
    }
    case 'didKey': {
      const algorithm = optional(auth, 'algorithm') ?? 'ES256'
      if (algorithm === 'EdDSA') throw unsupported('didKey with EdDSA: the client signs ES256 only')
      if (algorithm !== 'ES256') throw invalid(`unknown algorithm '${algorithm}'`)
      const pair = generateKeyPairSync('ec', { namedCurve: 'P-256' })
      const jwk = pair.privateKey.export({ format: 'jwk' })
      const did = didKeyP256(jwk)
      const kid = `${did}#${did.slice('did:key:'.length)}`
      next.selfIssued = { subject: did, keyId: kid, jwk }
      result.agent = did
      result.kid = kid
      break
    }
    default:
      throw invalid(`unknown auth type '${auth.type}'`)
  }
  configured = { ...configured, session: undefined, selfIssued: undefined, subjectToken: undefined, subjectTokenType: undefined, ...next }
  client = null
  await theClient()
  return result
}

// ---------------------------------------------------------------------------
// Operations

async function run (kind, url, extra = {}) {
  return (await theClient()).run({ ...extra, kind, url })
}

const operations = {
  configure,

  async discover_storage (args) {
    const done = await run('discover', targetOf(args, 'url'))
    return storageOf(done.description)
  },

  async get_storage_description (args) {
    const url = targetOf(args, 'url')
    const done = await run('read', url)
    const desc = jsonOfDone(done)
    if (desc === undefined || typeof desc !== 'object') throw new AdapterError('ProtocolError', 'the storage description is not JSON')
    return storageOf(desc)
  },

  async head (args) {
    const url = targetOf(args, 'url')
    return metadataFrom(url, await run('head', url))
  },

  async read (args) {
    const url = targetOf(args, 'url')
    for (const name of ['rangeStart', 'rangeEnd', 'ifNoneMatch', 'prefer']) {
      if (args[name] !== undefined && args[name] !== null) throw unsupported(`read option '${name}': the client's read has no such option`)
    }
    const extra = {}
    const accept = optional(args, 'accept')
    if (accept !== undefined) extra.accept = accept
    const done = await run('read', url, extra)
    const metadata = metadataFrom(url, done)
    return { metadata, notModified: done.status === 304, body: bodyResult(bytesOfDone(done), metadata.contentType) }
  },

  async read_container (args) {
    const url = targetOf(args, 'url')
    const done = await run('read', url)
    const metadata = metadataFrom(url, done)
    const doc = jsonOfDone(done)
    if (doc === undefined || typeof doc !== 'object') throw new AdapterError('ProtocolError', 'the container page is not JSON')
    const rel = (r) => metadata.links.find((l) => l.rel === r)?.href
    return {
      id: absolute(url, doc.id), types: asList(doc.type), totalItems: doc.totalItems,
      items: asList(doc.items).map((m) => itemOf(m, url)),
      first: rel('first'), next: rel('next'), prev: rel('prev'), last: rel('last'), metadata
    }
  },

  async list_container (args) {
    const url = targetOf(args, 'url')
    const limit = limitOf(args)
    const done = await run('list', url)
    const members = asList(done.members)
    return { items: members.slice(0, limit).map((m) => itemOf(m, url)), truncated: members.length > limit }
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
    if (links !== undefined) extra.links = links.map((l) => `<${l.href}>; rel="${l.rel}"`)
    const done = await run('create', container, extra)
    return { location: done.location, metadata: metadataFrom(done.location ?? container, done) }
  },

  async create_container (args) {
    const parent = targetOf(args, 'parent')
    const extra = { container: true }
    const slug = optional(args, 'slug')
    if (slug !== undefined) extra.slug = slug
    const done = await run('create', parent, extra)
    return { location: done.location, metadata: metadataFrom(done.location ?? parent, done) }
  },

  async update (args) {
    const url = targetOf(args, 'url')
    if (args.body === undefined || args.body === null) throw invalid("missing argument 'body'")
    const { bytes, contentType } = bodyOf(args.body, optional(args, 'contentType'))
    const extra = { body: bytes, ...preconditionOf(args) }
    if (contentType !== undefined) extra.mediaType = contentType
    const done = await run('update', url, extra)
    const metadata = metadataFrom(url, done)
    return { status: done.status, etag: metadata.etag, metadata }
  },

  async patch (args) {
    const url = targetOf(args, 'url')
    if (args.ifNoneMatch !== undefined && args.ifNoneMatch !== null) throw unsupported('ifNoneMatch on patch')
    const extra = { body: patchBody(args.patch), ...preconditionOf(args) }
    const done = await run('patch', url, extra)
    const metadata = metadataFrom(url, done)
    return { status: done.status, etag: metadata.etag, metadata }
  },

  async delete (args) {
    const url = targetOf(args, 'url')
    const extra = { ...preconditionOf(args) }
    if (optional(args, 'recursive', 'boolean')) extra.recursive = true
    await run('delete', url, extra)
    return {}
  },

  async linkset_url (args) {
    const url = targetOf(args, 'url')
    const done = await run('readLinkset', url)
    remember(url, done.url)
    return { linkset: done.url }
  },

  async read_linkset (args) {
    const url = targetOf(args, 'url')
    const done = await run('readLinkset', url)
    remember(url, done.url)
    return {
      url: done.url, etag: done.etag === '' ? undefined : done.etag, linkset: done.linkset,
      allow: asList(done.allow), acceptPatch: asList(done.acceptPatch)
    }
  },

  async update_linkset (args) {
    const linksetUrl = targetOf(args, 'linksetUrl')
    const doc = required(args, 'linkset', 'object')
    if (!Array.isArray(doc.linkset)) throw invalid("argument 'linkset' must be a linkset document")
    const resource = ownerOf(linksetUrl)
    const extra = { body: new TextEncoder().encode(JSON.stringify(doc)), mediaType: 'application/linkset+json', ...preconditionOf({ ifMatch: args.ifMatch }) }
    const done = await run('updateLinkset', resource, extra)
    const metadata = metadataOf(linksetUrl, done.status, done.headers)
    return { status: done.status, etag: metadata.etag, metadata }
  },

  async patch_linkset (args) {
    const linksetUrl = targetOf(args, 'linksetUrl')
    const resource = ownerOf(linksetUrl)
    const extra = { body: patchBody(args.patch), ...preconditionOf({ ifMatch: args.ifMatch }) }
    const done = await run('updateLinkset', resource, extra)
    const metadata = metadataOf(linksetUrl, done.status, done.headers)
    return { status: done.status, etag: metadata.etag, metadata }
  },

  async move (args) {
    const url = targetOf(args, 'url')
    const destination = targetOf(args, 'destination')
    const extra = { destination, ...preconditionOf({ ifMatch: args.ifMatch }) }
    const done = await run('move', url, extra)
    const location = done.identifier ?? url
    // The move answers for the linkset; the resource's metadata is a head of its new place.
    const head = await run('head', location)
    const metadata = metadataFrom(location, head)
    return {
      status: done.status, location, linkset: metadata.linkset, identifierPreserved: location === url,
      etag: metadata.etag, metadata
    }
  },

  async subscribe (args) {
    const serviceUrl = targetOf(args, 'serviceUrl')
    const topics = required(args, 'topics', 'array')
    const inbox = required(args, 'inbox')
    if (optional(args, 'expires') !== undefined) throw unsupported("subscribe option 'expires': the client's subscribe has no such option")
    const done = await run('subscribe', serviceUrl, { topics, inbox })
    return subscriptionOf(done.location ?? serviceUrl, done)
  },

  async list_subscriptions (args) {
    const serviceUrl = targetOf(args, 'serviceUrl')
    const limit = limitOf(args)
    const done = await run('list', serviceUrl)
    const members = asList(done.members)
    return { items: members.slice(0, limit).map((m) => itemOf(m, serviceUrl)), truncated: members.length > limit }
  },

  async get_subscription (args) {
    const url = targetOf(args, 'url')
    return subscriptionOf(url, await run('read', url))
  },

  async unsubscribe (args) {
    await run('unsubscribe', targetOf(args, 'url'))
    return {}
  },

  async verify_notification (args) {
    const url = targetOf(args, 'url')
    const method = required(args, 'method')
    const headers = required(args, 'headers', 'object')
    const body = base64Bytes(required(args, 'bodyBase64'), 'bodyBase64')
    if (args.trustedStorages !== undefined && args.trustedStorages !== null) {
      throw unsupported("verify_notification option 'trustedStorages': the client's receiver has no such option")
    }
    const pairs = []
    for (const [name, value] of Object.entries(headers)) for (const v of asList(value)) pairs.push([name, String(v)])
    const done = await run('verifyNotification', url, { method, headers: pairs, body })
    if (done.accept !== true) throw new AdapterError('SignatureVerificationError', `${done.reason ?? 'the notification was refused'} (status ${done.status})`)
    // REPORTING: what the accepted delivery says about itself.
    const h = headerMap(pairs)
    const keyid = /keyid="([^"]*)"/.exec(h.get('signature-input') ?? '')?.[1] ?? ''
    let raw
    try { raw = JSON.parse(new TextDecoder().decode(body)) } catch { raw = {} }
    const one = (a) => ({ id: a.id, types: asList(a.type), object: typeof a.object === 'string' ? a.object : a.object?.id, objectTypes: asList(a.object?.type) })
    return { storage: typeof raw.storage === 'string' ? raw.storage : keyid.split('#')[0], keyid, activities: asList(raw.activity ?? raw.activities).map(one), raw }
  },

  async request_access (args) {
    const request = required(args, 'request', 'object')
    return accessWrite('requestAccess', args, request, 'AccessRequest')
  },

  async get_access_request (args) {
    const done = await run('getAccess', targetOf(args, 'url'))
    return { document: jsonOfDone(done) }
  },

  async list_access_requests (args) {
    return listService(args)
  },

  async cancel_access_request (args) {
    await run('delete', targetOf(args, 'url'))
    return {}
  },

  async grant_access (args) {
    const grant = required(args, 'grant', 'object')
    return accessWrite('grantAccess', args, grant, 'AccessGrant')
  },

  async get_access_grant (args) {
    const done = await run('getAccess', targetOf(args, 'url'))
    return { document: jsonOfDone(done) }
  },

  async list_access_grants (args) {
    return listService(args)
  },

  async revoke_access_grant (args) {
    await run('revokeAccess', targetOf(args, 'url'))
    return {}
  },

  async read_type_index (args) {
    const serviceUrl = targetOf(args, 'url')
    const done = await run('typeIndex', insideStorage(serviceUrl))
    return { types: asList(done.items) }
  },

  async list_types (args) {
    const serviceUrl = targetOf(args, 'serviceUrl')
    const limit = limitOf(args)
    const done = await run('typeIndex', insideStorage(serviceUrl))
    const types = asList(done.items)
    return { types: types.slice(0, limit), truncated: types.length > limit }
  },

  async search_all (args) {
    const serviceUrl = targetOf(args, 'serviceUrl')
    const query = queryOf(required(args, 'query', 'object'))
    const limit = limitOf(args)
    const done = await run('search', insideStorage(serviceUrl), { query })
    const members = asList(done.members)
    return { items: members.slice(0, limit).map((m) => itemOf(m, serviceUrl)), truncated: members.length > limit }
  },

  async shutdown () {
    return {}
  }
}

/** The client's request and grant documents are made from an operation's
 *  members (actions, assignee, targets, constraint, inbox), not from a document. */
async function accessWrite (kind, args, doc, type) {
  const serviceUrl = targetOf(args, 'serviceUrl')
  const policies = asList(doc.access)
  if (policies.length !== 1) throw unsupported(`${type} with ${policies.length} policies: the client writes one policy`)
  const policy = policies[0]
  const target = policy.target
  const targets = asList(target?.value ?? target).filter((t) => typeof t === 'string')
  const extra = { actions: asList(policy.action), assignee: policy.assignee, targets }
  if (policy.constraint !== undefined) extra.constraint = policy.constraint
  if (typeof doc.inbox === 'string') extra.inbox = doc.inbox
  const done = await run(kind, serviceUrl, extra)
  return { location: done.location }
}

/** The resource whose linkset this is, as the client reported it earlier. */
function ownerOf (linksetUrl) {
  const owner = linksetOwners.get(linksetUrl)
  if (owner === undefined) {
    throw unsupported('the client addresses a linkset through its resource, and this adapter has not seen which resource has this linkset (head, read, linkset_url or read_linkset of the resource first)')
  }
  return owner
}

async function listService (args) {
  const serviceUrl = targetOf(args, 'serviceUrl')
  const limit = limitOf(args)
  const done = await run('list', serviceUrl)
  const members = asList(done.members)
  return { items: members.slice(0, limit).map((m) => itemOf(m, serviceUrl)), truncated: members.length > limit }
}

// Operations of the protocol this client does not have (README.md, "Unsupported").
const UNSUPPORTED = {
  search_types: 'the client follows every result page and does not return one page',
  accepted_query_formats: 'the client has no operation that reads the accepted query formats'
}
for (const [name, why] of Object.entries(UNSUPPORTED)) {
  operations[name] = async () => { throw unsupported(why) }
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
    operations: Object.keys(operations).filter((name) => !Object.hasOwn(UNSUPPORTED, name))
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
