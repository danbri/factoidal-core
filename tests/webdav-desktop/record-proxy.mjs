// A recording HTTP proxy for WebDAV clients.
// https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
//
// The proxy listens on 127.0.0.1, forwards every request unchanged to the
// `webdav-serve` origin, and writes one JSON line per request to a log:
// method, path, request headers, the first bytes of XML request bodies, the
// status, response headers, the first bytes of the response body (for
// PROPFIND, LOCK and every 4xx or 5xx), sizes and the time taken. The log
// shows what Finder, Windows Explorer, GNOME Files or Dolphin sent, which the
// file browser does not tell its user.
//
// It makes no protocol decision: no status, header or body is changed. The
// Host header goes upstream as the client sent it, so `Destination` URLs in
// COPY and MOVE stay consistent with it. Authorization and Cookie values are
// replaced by "(removed)" in the log, never written.
//
//   import { startRecordingProxy } from './record-proxy.mjs'
//   const p = await startRecordingProxy({ target: 'http://127.0.0.1:8090', port: 8091, logFile })
//   ...; await p.close()

import { createServer, request as httpRequest } from 'node:http'
import { appendFileSync } from 'node:fs'

/** Bytes of a body kept in the log. */
export const BODY_SAMPLE = 4096

const XMLISH = /xml|text|json/i
const KEEP_RESPONSE_BODY = new Set(['PROPFIND', 'LOCK', 'PROPPATCH', 'OPTIONS'])
const REMOVE = new Set(['authorization', 'cookie', 'proxy-authorization'])

function scrubbed (headers) {
  const out = {}
  for (const [k, v] of Object.entries(headers)) out[k] = REMOVE.has(k.toLowerCase()) ? '(removed)' : v
  return out
}

function safeDecode (path) {
  try { return decodeURIComponent(path) } catch (_e) { return null }
}

/**
 * Start the proxy. Resolves when it listens.
 * @param {{ target: string, port?: number, host?: string, logFile: string, onRecord?: (r: object) => void }} options
 * @returns {Promise<{ origin: string, port: number, close: () => Promise<void>, count: () => number }>}
 */
export function startRecordingProxy ({ target, port = 0, host = '127.0.0.1', logFile, onRecord }) {
  const up = new URL(target)
  let seq = 0
  const server = createServer((req, res) => {
    const id = ++seq
    const started = process.hrtime.bigint()
    const record = {
      seq: id,
      t: new Date().toISOString(),
      method: req.method,
      url: req.url,
      path: safeDecode((req.url || '').split('?')[0]),
      ua: req.headers['user-agent'] || null,
      reqHeaders: scrubbed(req.headers),
      reqBytes: 0,
      reqBody: null,
      status: null,
      resHeaders: null,
      resBytes: 0,
      resBody: null,
      ms: null,
      error: null
    }
    const reqChunks = []
    let reqKept = 0
    const keepReq = XMLISH.test(req.headers['content-type'] || '') || ['PROPFIND', 'PROPPATCH', 'LOCK'].includes(req.method)
    const upstream = httpRequest({
      host: up.hostname,
      port: up.port,
      method: req.method,
      path: req.url,
      headers: req.headers
    }, (ures) => {
      record.status = ures.statusCode
      record.resHeaders = ures.headers
      res.writeHead(ures.statusCode, ures.statusMessage, ures.rawHeaders)
      const keepRes = KEEP_RESPONSE_BODY.has(req.method) || ures.statusCode >= 400
      const resChunks = []
      let resKept = 0
      ures.on('data', (c) => {
        record.resBytes += c.length
        if (keepRes && resKept < BODY_SAMPLE) { resChunks.push(c.subarray(0, BODY_SAMPLE - resKept)); resKept += Math.min(c.length, BODY_SAMPLE - resKept) }
        res.write(c)
      })
      ures.on('end', () => {
        res.end()
        if (keepRes) record.resBody = Buffer.concat(resChunks).toString('utf8')
        finish()
      })
      ures.on('error', (e) => { record.error = `upstream response: ${e.message}`; res.destroy(); finish() })
    })
    upstream.on('error', (e) => {
      record.error = `upstream: ${e.message}`
      if (!res.headersSent) { res.writeHead(502, { 'content-type': 'text/plain' }); res.end('record-proxy: upstream failed\n') } else res.destroy()
      finish()
    })
    req.on('data', (c) => {
      record.reqBytes += c.length
      if (keepReq && reqKept < BODY_SAMPLE) { reqChunks.push(c.subarray(0, BODY_SAMPLE - reqKept)); reqKept += Math.min(c.length, BODY_SAMPLE - reqKept) }
      upstream.write(c)
    })
    req.on('end', () => upstream.end())
    req.on('aborted', () => { record.error = 'client aborted'; upstream.destroy() })
    let done = false
    function finish () {
      if (done) return
      done = true
      if (keepReq) record.reqBody = Buffer.concat(reqChunks).toString('utf8')
      record.ms = Number(process.hrtime.bigint() - started) / 1e6
      appendFileSync(logFile, JSON.stringify(record) + '\n')
      if (onRecord) onRecord(record)
    }
  })
  return new Promise((resolve, reject) => {
    server.once('error', reject)
    server.listen(port, host, () => {
      const p = server.address().port
      resolve({
        origin: `http://${host}:${p}`,
        port: p,
        count: () => seq,
        close: () => new Promise((r) => { server.closeAllConnections?.(); server.close(() => r()) })
      })
    })
  })
}
