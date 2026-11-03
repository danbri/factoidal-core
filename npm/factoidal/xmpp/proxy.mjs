// factoidal/xmpp/proxy.mjs — `factoidal xmpp-http-proxy`: a local HTTP
// listener whose every request is sent over XMPP (XEP-0332) to ONE target
// JID, so a file browser, rclone, curl or our LWS client can use
// http://127.0.0.1:PORT/ to reach `webdav-serve --xmpp` behind NAT.
// https://github.com/danbri/factoidal/issues/1107 (step 2). Design record:
// docs/designissues/2026-10-28-http-over-xmpp.md, section "Step 2".
//
// WHAT THIS FILE IS ALLOWED TO DO
// Listen on the address the engine accepted (`listenHost`, 127.0.0.1 only in
// this step), read each HTTP request (method, request target, raw header
// pairs, body up to the engine's `maxBodyBytes` plus one byte), give it to
// `connectHttpRequester().request`, and write the status, header pairs and
// body it resolves with. No protocol decision: which headers are forwarded,
// where the stanzas go, the refusals, limits, timeouts and every status are
// decided in formal/lean4/L4Factoidal/XMPP/HttpRequester.lean and
// formal/lean4/Wasm/Ops/XmppClient.lean.

import http from 'node:http'
import { connectHttpRequester } from './client.mjs'

/**
 * Start the proxy. Resolves when the XMPP stream is bound and the listener
 * is open.
 *
 * @param {object} options the options of `connectHttpRequester` (jid,
 *   password, target, host, port, tls, tlsOptions, timeoutSeconds, engine,
 *   onError), plus:
 * @param {string} [options.listenHost] default 127.0.0.1 (the engine refuses any other)
 * @param {number} [options.listenPort] default 8091; 0 takes an ephemeral port
 * @returns {Promise<{origin: string, jid: string, target: string, closed: Promise<string>, close: Function}>}
 */
export async function startHttpProxy (options = {}) {
  const onError = typeof options.onError === 'function' ? options.onError : () => {}
  const conn = await connectHttpRequester({
    ...options,
    listenHost: typeof options.listenHost === 'string' ? options.listenHost : '127.0.0.1'
  })
  const limit = conn.maxBodyBytes

  const server = http.createServer((req, res) => {
    const parts = []
    let size = 0
    req.on('data', (b) => {
      // Keep at most limit + 1 bytes: enough for the engine to answer 413.
      if (size > limit) return
      parts.push(b)
      size += b.length
    })
    req.on('end', async () => {
      const headers = []
      for (let i = 0; i + 1 < req.rawHeaders.length; i += 2) headers.push([req.rawHeaders[i], req.rawHeaders[i + 1]])
      let body = Buffer.concat(parts)
      if (body.length > limit + 1) body = body.subarray(0, limit + 1)
      let answer
      try {
        answer = await conn.request({ method: req.method, target: req.url, headers, body })
      } catch (error) {
        onError(error)
        answer = { status: 502, headers: [['content-type', 'text/plain; charset=utf-8']], body: Buffer.from(`proxy host error: ${error.message}\n`) }
      }
      const flat = []
      for (const [n, v] of answer.headers) flat.push(n, v)
      try {
        res.writeHead(answer.status, flat)
        res.end(Buffer.from(answer.body))
      } catch (error) {
        onError(error)
        if (!res.headersSent) { res.writeHead(502); res.end() } else res.destroy()
      }
    })
    req.on('error', (error) => onError(error))
  })
  // Node gives CONNECT as its own event, with the raw socket. The request
  // goes to the engine like any other (it answers 405); the answer is written
  // on the socket, which is then closed. No tunnel is ever opened.
  server.on('connect', async (req, socket) => {
    const headers = []
    for (let i = 0; i + 1 < req.rawHeaders.length; i += 2) headers.push([req.rawHeaders[i], req.rawHeaders[i + 1]])
    let answer
    try {
      answer = await conn.request({ method: req.method, target: req.url, headers, body: new Uint8Array(0) })
    } catch (error) {
      onError(error)
      answer = { status: 502, headers: [], body: new Uint8Array(0) }
    }
    const body = Buffer.from(answer.body)
    const lines = [`HTTP/1.1 ${answer.status} ${http.STATUS_CODES[answer.status] || ''}`]
    for (const [n, v] of answer.headers) lines.push(`${n}: ${v}`)
    lines.push(`content-length: ${body.length}`, 'connection: close', '', '')
    socket.end(Buffer.concat([Buffer.from(lines.join('\r\n'), 'latin1'), body]))
  })
  const port = typeof options.listenPort === 'number' ? options.listenPort : 8091
  try {
    await new Promise((resolve, reject) => {
      server.once('error', reject)
      server.listen(port, conn.listenHost, resolve)
    })
  } catch (error) {
    await conn.close()
    throw error
  }
  const addr = server.address()
  conn.closed.then(() => server.close())
  return {
    origin: `http://${addr.address}:${addr.port}/`,
    jid: conn.jid,
    target: conn.target,
    closed: conn.closed,
    async close () {
      server.close()
      await conn.close()
    }
  }
}
