// Put a lab tree into a WebDAV mount, and list a mount, with plain HTTP.
// https://github.com/danbri/factoidal/issues/1079
//
// A client of the WebDAV server only: MKCOL, PUT, PROPFIND. It records the
// status of every request, so a name the server refuses is a result.

import { request as httpRequest } from 'node:http'

/** Percent-encode each segment of a slash path (every byte outside unreserved). */
export function encodePath (path) {
  return path.split('/').map((s) => encodeURIComponent(s).replace(/[!'()*]/g, (c) => '%' + c.charCodeAt(0).toString(16).toUpperCase())).join('/')
}

/** One HTTP request. Resolves { status, headers, body: Buffer }. */
export function davRequest (origin, method, path, { headers = {}, body = null } = {}) {
  const u = new URL(origin)
  return new Promise((resolve, reject) => {
    const req = httpRequest({ host: u.hostname, port: u.port, method, path, headers: { ...headers, ...(body !== null ? { 'content-length': body.length } : {}) } }, (res) => {
      const chunks = []
      res.on('data', (c) => chunks.push(c))
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks) }))
      res.on('error', reject)
    })
    req.on('error', reject)
    if (body !== null) req.end(body)
    else req.end()
  })
}

const CONTENT_TYPES = {
  txt: 'text/plain; charset=utf-8', md: 'text/markdown; charset=utf-8', csv: 'text/csv; charset=utf-8',
  json: 'application/json', jsonld: 'application/ld+json', ttl: 'text/turtle', rq: 'application/sparql-query',
  srj: 'application/sparql-results+json', html: 'text/html; charset=utf-8', svg: 'image/svg+xml',
  png: 'image/png', pdf: 'application/pdf', log: 'text/plain; charset=utf-8', ini: 'text/plain',
  // Link files: GLib (gvfs) takes the type from DAV:getcontenttype, so a
  // .desktop file served as text/plain is not a launcher there (probe-linux,
  // 2026-10-28). These are the shared-mime-info names.
  desktop: 'application/x-desktop', url: 'application/x-mswinurl', webloc: 'application/x-webloc'
}

/** A Content-Type for a file name, from its extension; default application/octet-stream. */
export function contentTypeFor (path) {
  const m = /\.([A-Za-z0-9]+)$/.exec(path)
  return (m && CONTENT_TYPES[m[1].toLowerCase()]) || 'application/octet-stream'
}

/**
 * Create the folders and files of `entries` under `/<mount>/`.
 * @param {string} origin the server origin (not the recording proxy)
 * @param {string} mount the mount name
 * @param {Array<{path: string, data?: Buffer, dir?: boolean}>} entries
 * @param {string[]} folders folders, parents first, each ending in '/'
 * @returns {Promise<Array<{ path: string, kind: string, status: number, ok: boolean }>>}
 */
export async function seedTree (origin, mount, entries, folders) {
  const out = []
  for (const f of folders) {
    const r = await davRequest(origin, 'MKCOL', `/${encodePath(mount)}/${encodePath(f.slice(0, -1))}/`)
    out.push({ path: f, kind: 'folder', status: r.status, ok: r.status === 201 || r.status === 405 })
  }
  for (const e of entries) {
    if (e.dir) continue
    const r = await davRequest(origin, 'PUT', `/${encodePath(mount)}/${encodePath(e.path)}`, { headers: { 'content-type': contentTypeFor(e.path) }, body: e.data })
    out.push({ path: e.path, kind: 'file', status: r.status, ok: r.status >= 200 && r.status < 300 })
  }
  return out
}

function decodeXmlText (s) {
  return s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&#(\d+);/g, (_m, d) => String.fromCodePoint(Number(d))).replace(/&#x([0-9a-fA-F]+);/g, (_m, h) => String.fromCodePoint(parseInt(h, 16))).replace(/&amp;/g, '&')
}

/** Parse a PROPFIND multistatus into [{ href, collection, size }]. Prefix-agnostic. */
export function parseMultistatus (xml) {
  const out = []
  const re = /<(?:[A-Za-z][\w.-]*:)?response\b[^>]*>([\s\S]*?)<\/(?:[A-Za-z][\w.-]*:)?response>/g
  let m
  while ((m = re.exec(xml)) !== null) {
    const part = m[1]
    const href = /<(?:[A-Za-z][\w.-]*:)?href\b[^>]*>([\s\S]*?)<\/(?:[A-Za-z][\w.-]*:)?href>/.exec(part)
    const len = /<(?:[A-Za-z][\w.-]*:)?getcontentlength\b[^>]*>(\d+)</.exec(part)
    out.push({
      href: href ? decodeXmlText(href[1].trim()) : null,
      collection: /<(?:[A-Za-z][\w.-]*:)?collection\s*\/>/.test(part),
      size: len ? Number(len[1]) : null
    })
  }
  return out
}

/**
 * Every member under `/<mount>/`, by PROPFIND Depth 1 on each collection.
 * @returns {Promise<Array<{ path: string, collection: boolean, size: number|null }>>} paths decoded, relative to the mount
 */
export async function walkMount (origin, mount) {
  const root = `/${encodePath(mount)}/`
  const out = []
  const queue = [root]
  const seen = new Set()
  while (queue.length > 0) {
    const href = queue.shift()
    if (seen.has(href)) continue
    seen.add(href)
    const r = await davRequest(origin, 'PROPFIND', href, { headers: { depth: '1', 'content-type': 'application/xml' }, body: Buffer.from('<?xml version="1.0"?><propfind xmlns="DAV:"><allprop/></propfind>') })
    if (r.status !== 207) throw new Error(`PROPFIND ${href}: ${r.status}`)
    for (const item of parseMultistatus(r.body.toString('utf8'))) {
      if (item.href === null) continue
      const path = new URL(item.href, 'http://x').pathname
      if (path === href) continue
      let rel
      try { rel = decodeURIComponent(path.slice(root.length)) } catch (_e) { rel = path.slice(root.length) }
      out.push({ path: rel, collection: item.collection, size: item.size })
      if (item.collection) queue.push(path.endsWith('/') ? path : path + '/')
    }
  }
  return out.sort((a, b) => (a.path < b.path ? -1 : 1))
}
