// The LWS reader of an SBM11 generation for lib/sbm11.mjs: the files of a
// generation (or of a collection root with its CURRENT pointer) stored as
// Linked Web Storage resources, one resource per file, under one container
// URL (https://github.com/danbri/factoidal/issues/1010 KR3, read part;
// LWS 1.0: https://w3c.github.io/lws-protocol/lws10-core/).
//
// WHAT THIS FILE IS ALLOWED TO DO
// Move bytes. The engine names every file and checks every length against
// the manifest (formal/lean4/L4Factoidal/Storage/Sbm11/HostSession.lean,
// through the storage medium of formal/lean4/L4Factoidal/Storage/Medium.lean).
// This file maps a file name to a resource URL, makes HTTP GETs, and hands
// the bytes over. It reads no manifest and no byte of a file.
//
// HTTP (RFC 9110 section 14): each read asks for `Range: bytes=a-b`. A
// partial answer is used only when it is status 206 and its Content-Range is
// exactly `bytes a-b/N`. Any other successful answer is the whole
// representation: it is kept in memory and every later read of that file is
// cut from it, with no further request. A changed entity tag between two
// reads of one file refuses the read (the bytes of two versions are never
// mixed). The engine checks every byte it decodes against the manifest's
// Merkle roots (openSbm11's default `verify: 'merkle'`), so it asks for whole
// 65,536-byte chunks and the `.merkle` sidecars; this file does no check.
// Limits: no eviction of the in-memory copies, no retry. Resource paths are
// confined to the configured container. A custom transport must independently
// refuse redirects before forwarding headers. Default Node fetch refuses them;
// default worker XHR accepts no caller headers and checks the final response URL
// only after sending. XHR may still use ambient same-origin browser cookies.
//
// EVIDENCE
// `evidence()` lists each resource read: { resource, etag, lastModified,
// requests, partial, bytes } -- `partial` the number of 206 answers. The
// store from openSbm11 answers it as `store.evidence`.
//
// SYNCHRONOUS TRANSPORT
// The engine is inside WebAssembly and asks for bytes synchronously, so the
// reader needs a synchronous GET: `transport(url, headers) -> { status,
// header(name) -> string | null, bytes: Uint8Array }`. In Node the default
// is lib/sync-http-node.mjs (fetch in a worker thread, Atomics.wait); in a
// browser worker it is a synchronous XMLHttpRequest. A browser window
// thread has neither: pass `transport` or run the engine in a worker.

// This reader grants its transport authority only within one HTTP container.
// A file is a raw relative filename/path, never a URL reference. Reject both
// literal traversal and encoded structural characters before attaching headers.
function containerUrl (url) {
  let base
  try { base = new URL(String(url)) } catch { throw new TypeError('lwsSbm11Reader: expected an absolute HTTP(S) container URL') }
  if (!['http:', 'https:'].includes(base.protocol) || base.username || base.password || /[?#]/.test(base.href)) {
    throw new TypeError('lwsSbm11Reader: container must be HTTP(S), without userinfo, query or fragment; use opts.auth/headers')
  }
  if (!base.pathname.endsWith('/')) base.pathname += '/'
  return base
}

function resourceUrl (base, file) {
  if (typeof file !== 'string' || file.length === 0 || file.length > 4096) {
    throw new TypeError('invalid relative resource path')
  }
  let probe = file
  for (;;) {
    if (/^[a-z][a-z0-9+.-]*:/i.test(probe) || /[\\?#\x00-\x1f\x7f]/.test(probe) ||
        probe.split('/').some(part => part === '' || part === '.' || part === '..') ||
        /%(?:2f|5c|3f|23)/i.test(probe)) {
      throw new TypeError('resource path must remain inside the configured container')
    }
    // Decode only for rejection, never for the requested filename. Each changed
    // pass shortens the string, so nested percent encodings are also bounded.
    const next = probe.replace(/%([a-f0-9]{2})/gi, (_match, hex) => String.fromCharCode(parseInt(hex, 16)))
    if (next === probe) break
    probe = next
  }
  const resource = new URL(file.split('/').map(encodeURIComponent).join('/'), base)
  if (resource.origin !== base.origin || !resource.pathname.startsWith(base.pathname)) {
    throw new TypeError('resource URL escaped the configured container')
  }
  return resource.href
}

/** A synchronous GET with XMLHttpRequest (a browser worker). */
export function xhrSyncTransport (url, headers) {
  const x = new XMLHttpRequest()
  x.open('GET', url, false)
  x.responseType = 'arraybuffer'
  for (const [k, v] of Object.entries(headers)) x.setRequestHeader(k, v)
  x.send()
  // XHR follows redirects internally. This rejects returned bytes, not the
  // already-sent request. Caller headers require an explicit trusted transport.
  if (x.responseURL !== new URL(url).href) throw new Error('LWS reader: redirected XHR resource refused')
  return {
    status: x.status,
    header: (name) => x.getResponseHeader(name),
    bytes: new Uint8Array(x.response || new ArrayBuffer(0))
  }
}

function parseContentRange (value) {
  const m = /^bytes\s+(\d+)-(\d+)\/(\d+|\*)$/.exec(String(value || '').trim())
  if (!m) return null
  return { first: Number(m[1]), last: Number(m[2]), total: m[3] === '*' ? null : Number(m[3]) }
}

function unsatisfiedTotal (value) {
  const m = /^bytes\s+\*\/(\d+)$/.exec(String(value || '').trim())
  return m ? Number(m[1]) : null
}

/**
 * A reader ({ readAt, size, evidence, close }) of the SBM11 files held as
 * LWS resources under the container `url`.
 *
 * @param {string} url absolute HTTP(S), no userinfo/query/fragment; container that holds CURRENT and the generation
 *   (or the generation container itself)
 * @param {object} [opts]
 * @param {Function} [opts.transport] trusted synchronous GET; must constrain redirect/header forwarding
 * @param {string} [opts.auth] a value for the Authorization header, such as
 *   `Bearer <access token>` (an LWS access token)
 * @param {object} [opts.headers] further request headers; browser use requires explicit trusted transport
 */
export function lwsSbm11Reader (url, opts = {}) {
  const base = containerUrl(url)
  const extra = { ...(opts.headers || {}) }
  if (opts.auth) extra.authorization = String(opts.auth)
  let transport = opts.transport
  if (typeof transport !== 'function') {
    if (typeof XMLHttpRequest === 'function' && typeof document === 'undefined') {
      if (Object.keys(extra).length > 0) throw new TypeError('lwsSbm11Reader: caller headers require an explicit redirect-safe transport; default XHR cannot constrain forwarding')
      transport = xhrSyncTransport
    } else {
      throw new TypeError('lwsSbm11Reader: no synchronous transport here; pass opts.transport (Node: @factoidal/core gives one)')
    }
  }
  // file -> { url, etag, lastModified, total, whole, requests, partial, bytes }
  const files = new Map()
  const errors = []

  function entry (file) {
    let e = files.get(file)
    if (!e) {
      let url
      try { url = resourceUrl(base, file) } catch (error) {
        fail(file, error.message)
        return null
      }
      e = { url, etag: null, lastModified: null, total: undefined, whole: null, requests: 0, partial: 0, bytes: 0 }
      files.set(file, e)
    }
    return e
  }

  function fail (file, message) {
    errors.push(`${file}: ${message}`)
    return null
  }

  function get (e, file, first, last) {
    const headers = { ...extra, range: `bytes=${first}-${last}` }
    let r
    try {
      r = transport(e.url, headers)
    } catch (error) {
      fail(file, `GET ${e.url}: ${error && error.message ? error.message : error}`)
      return null
    }
    e.requests += 1
    const tag = r.header('etag')
    if (r.status >= 200 && r.status < 300) {
      if (e.etag !== null && tag !== e.etag) {
        fail(file, `the entity tag changed from ${e.etag} to ${tag}`)
        return null
      }
      e.etag = tag
      e.lastModified = r.header('last-modified')
      e.bytes += r.bytes.length
    }
    return r
  }

  function sizeOf (file) {
    const e = entry(file)
    if (e === null) return null
    if (e.total !== undefined) return e.total
    const r = get(e, file, 0, 0)
    if (r === null) return null
    const cr = parseContentRange(r.header('content-range'))
    if (r.status === 206 && cr && cr.first === 0 && cr.last === 0 && cr.total !== null && r.bytes.length === 1) {
      e.partial += 1
      e.total = cr.total
    } else if (r.status === 416 && unsatisfiedTotal(r.header('content-range')) !== null) {
      e.total = unsatisfiedTotal(r.header('content-range'))
      e.whole = new Uint8Array(0)
    } else if (r.status === 200) {
      e.whole = r.bytes
      e.total = r.bytes.length
    } else if (r.status === 404 || r.status === 410) {
      e.total = null
    } else {
      fail(file, `GET ${e.url}: status ${r.status}`)
      return null
    }
    return e.total
  }

  return {
    readAt (file, offset, length) {
      const e = entry(file)
      if (e === null) return null
      if (length === 0) return new Uint8Array(0)
      if (e.whole !== null) {
        return offset + length <= e.whole.length ? e.whole.subarray(offset, offset + length) : null
      }
      const last = offset + length - 1
      const r = get(e, file, offset, last)
      if (r === null) return null
      const cr = parseContentRange(r.header('content-range'))
      if (r.status === 206 && cr && cr.first === offset && cr.last === last && r.bytes.length === length) {
        e.partial += 1
        return r.bytes
      }
      if (r.status === 200) {
        e.whole = r.bytes
        e.total = r.bytes.length
        return offset + length <= r.bytes.length ? r.bytes.subarray(offset, offset + length) : null
      }
      return fail(file, `GET ${e.url} bytes ${offset}-${last}: status ${r.status}`)
    },
    size (file) {
      return sizeOf(file)
    },
    /** Each resource read: { resource, etag, lastModified, requests, partial, bytes }. */
    evidence () {
      const out = []
      for (const e of files.values()) {
        if (e.requests === 0 || e.etag === null) continue
        out.push({ resource: e.url, etag: e.etag, lastModified: e.lastModified, requests: e.requests, partial: e.partial, bytes: e.bytes })
      }
      return out
    },
    /** The transport failures, as text (a failed read reaches the engine as no bytes). */
    errors () { return errors.slice() },
    close () {
      files.clear()
      if (typeof opts.onClose === 'function') opts.onClose()
    }
  }
}
