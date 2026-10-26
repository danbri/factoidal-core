// A synchronous HTTP GET for Node, for the readers of lib/sbm11.mjs that read
// over HTTP (lib/sbm11-lws.mjs; https://github.com/danbri/factoidal/issues/1010).
// The engine is inside WebAssembly and asks for bytes synchronously; Node's
// fetch is asynchronous. A worker thread makes the fetch; this thread waits
// on a shared Int32Array (Atomics.wait) and takes the answer with
// receiveMessageOnPort. Pure I/O: no header is read here, no status judged.
//
// The thread that calls the transport is blocked until the answer comes, so
// the server must not run on that thread (start it in another process or
// worker).

import { Worker, MessageChannel, receiveMessageOnPort } from 'node:worker_threads'

const WORKER = `
const { workerData } = require('node:worker_threads')
const { port, signal } = workerData
const flag = new Int32Array(signal)
port.on('message', async (req) => {
  let out
  try {
    const r = await fetch(req.url, { headers: req.headers, redirect: 'follow' })
    const headers = {}
    r.headers.forEach((v, k) => { headers[k] = v })
    out = { status: r.status, headers, bytes: new Uint8Array(await r.arrayBuffer()) }
  } catch (e) {
    out = { error: String(e && e.message ? e.message : e) }
  }
  port.postMessage(out)
  Atomics.store(flag, 0, 1)
  Atomics.notify(flag, 0)
})
`

/**
 * A synchronous transport `(url, headers) -> { status, header(name), bytes }`
 * with a `close()` that stops its worker.
 *
 * @param {object} [opts]
 * @param {number} [opts.timeoutMs] the most one request may take (default 60000)
 */
export function nodeSyncTransport (opts = {}) {
  const timeoutMs = typeof opts.timeoutMs === 'number' ? opts.timeoutMs : 60000
  const signal = new SharedArrayBuffer(4)
  const flag = new Int32Array(signal)
  const { port1, port2 } = new MessageChannel()
  const worker = new Worker(WORKER, { eval: true, workerData: { port: port2, signal }, transferList: [port2] })
  worker.unref()
  port1.unref()
  let closed = false
  function transport (url, headers) {
    if (closed) throw new Error('the transport is closed')
    Atomics.store(flag, 0, 0)
    port1.postMessage({ url: String(url), headers: { ...headers } })
    if (Atomics.wait(flag, 0, 0, timeoutMs) === 'timed-out') {
      throw new Error(`GET ${url}: no answer in ${timeoutMs} ms`)
    }
    const got = receiveMessageOnPort(port1)
    if (!got) throw new Error(`GET ${url}: no answer from the transport worker`)
    const m = got.message
    if (m.error) throw new Error(m.error)
    const h = m.headers
    return { status: m.status, header: (name) => (Object.hasOwn(h, name.toLowerCase()) ? h[name.toLowerCase()] : null), bytes: m.bytes }
  }
  transport.close = () => {
    if (closed) return
    closed = true
    port1.close()
    worker.terminate()
  }
  return transport
}
