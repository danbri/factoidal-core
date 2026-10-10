// `factoidal serve`: a SPARQL 1.1 Protocol, Graph Store Protocol and Service
// Description endpoint over one activated Shardborough collection.
// https://github.com/danbri/factoidal/issues/669
//
// WHAT THIS FILE IS ALLOWED TO DO
// Accept TCP connections, hand the bytes a connection delivered to the
// engine's `storeServeRequest`, write the bytes the engine answers, read the
// store files the engine names, and append the bytes the engine hands back
// to the file it names, at the size it names. That is the whole contract.
//
// It makes NO HTTP and NO SPARQL decision. It does not know where a request
// ends (Content-Length and chunked framing are in
// `formal/lean4/L4Factoidal/HTTP/Wire.lean`), what a header means, which
// endpoint a path is, which status a request earns, which media type an
// answer takes, or what an update changes. All of that is in
// `formal/lean4/L4Factoidal/SPARQL/StoreEndpoint.lean` and the protocol
// modules it calls (iron rule 7 of CLAUDE.md). It reads no manifest field,
// decodes no block and computes no digest: the engine names the files to
// read (`storeServeKeys`) and verifies them (`storeServeOpen`).
//
// The one status this file writes itself is 500, and only when the engine
// call throws or the host cannot write: a failure of this host.
//
// THE WASM CONTRACT (`formal/lean4/Wasm/Ops/StoreServe.lean`)
//   storeServeKeys    [manifestHex]                 -> { keys, state }
//   storeServeOpen    [manifestHex, artifactsJson, stateJson, configJson]
//                     + region                       -> { handle, ... }
//   storeServeRequest [handle] + the connection's bytes
//       -> { state: 'incomplete', need? }
//        | { state: 'respond', consumed, close, status } + response bytes
//        | { state: 'append', consumed, close, pending, key, expectedSize }
//          + the bytes to append
//   storeServeCommit  [handle, pending, outcome]   -> { state: 'respond',
//                                                       close, status }
//                                                     + response bytes
//   storeServeClose   [handle]                       -> {}
//
// An update is two calls. The engine answers `append`; this host appends
// the bytes to the named file only if the file has exactly `expectedSize`
// bytes, syncs it, and reports "ok" (or why not) to `storeServeCommit`,
// which answers the response either way. The append is synchronous, so no
// other request is served between the two calls.
//
// Concurrency: one engine instance, single-threaded; connections are served
// one engine call at a time. Several processes must not serve one
// collection for writing: the append has no advisory lock
// (https://github.com/danbri/factoidal/issues/644).

import {
  StoreHostError, appendSyncAtSize, openCollection, readWhole
} from '../store-host/index.mjs'
import { joinPath, requireChildName } from '../store-host/paths.mjs'
import { hexOfBytes, loadEngine } from './engine.mjs'

/** The ops this host needs from the engine. */
export const SERVE_OPS = [
  'storeServeKeys', 'storeServeOpen', 'storeServeRequest', 'storeServeCommit',
  'storeServeClose'
]

/** A failure of this host, as opposed to an answer of the engine.
 *  `unknownOp` is set when the loaded module does not carry the ops. */
export class ServeHostError extends Error {
  constructor (message, detail = {}) {
    super(message)
    this.name = 'ServeHostError'
    this.unknownOp = detail.unknownOp === true
  }
}

function isUnknownOp (error) {
  const text = error && error.message ? String(error.message) : String(error)
  return text.indexOf('unknown op') >= 0
}

function concatenate (chunks) {
  let total = 0
  for (const chunk of chunks) total += chunk.length
  const out = new Uint8Array(total)
  let offset = 0
  for (const chunk of chunks) {
    out.set(chunk, offset)
    offset += chunk.length
  }
  return out
}

/** Read one file the engine named, or null when it does not exist. */
function readOptional (path) {
  try {
    return readWhole(path)
  } catch (error) {
    if (error instanceof StoreHostError && error.code === 'OPEN_FAILED') return null
    throw error
  }
}

/**
 * Open the activated generation of a collection for serving.
 *
 * Reads CURRENT and the manifest, asks the engine which files it needs,
 * reads them, and hands every byte to `storeServeOpen` in one region.
 *
 * @param {string} root the collection root that holds CURRENT
 * @param {object} [options]
 * @param {object} [options.engine] an engine handle to reuse
 * @param {string} [options.queryPath] the query and update endpoint path
 * @param {string} [options.gspPath] the Graph Store endpoint path
 * @returns {Promise<object>} the served store: `request(bytes)`,
 *   `commit(pending, outcome)`, `close()`, `info`, `generationDir`
 */
export async function openServedStore (root, options = {}) {
  const engine = options.engine !== undefined ? options.engine : await loadEngine()
  const opened = openCollection(root)
  const manifestHex = hexOfBytes(opened.manifest)
  let named
  try {
    named = engine.call('storeServeKeys', [manifestHex])
  } catch (error) {
    if (isUnknownOp(error)) {
      throw new ServeHostError(
        'the loaded l4factoidal WebAssembly module does not carry the storeServe ops ' +
        '(rebuild formal/lean4/Wasm)', { unknownOp: true })
    }
    throw error
  }
  const chunks = []
  const artifacts = []
  const state = []
  let offset = 0
  for (const key of named.keys) {
    const bytes = readWhole(joinPath(opened.generationDir, requireChildName(key, 'artifact key')))
    artifacts.push({ key, offset, len: bytes.length })
    chunks.push(bytes)
    offset += bytes.length
  }
  for (const key of named.state) {
    const bytes = readOptional(joinPath(opened.generationDir, requireChildName(key, 'state key')))
    if (bytes === null) continue
    state.push({ key, offset, len: bytes.length })
    chunks.push(bytes)
    offset += bytes.length
  }
  const config = {}
  if (typeof options.queryPath === 'string') config.queryPath = options.queryPath
  if (typeof options.gspPath === 'string') config.gspPath = options.gspPath
  const info = engine.callBlobIO('storeServeOpen',
    [manifestHex, JSON.stringify(artifacts), JSON.stringify(state), JSON.stringify(config)],
    concatenate(chunks)).envelope
  const handle = info.handle
  return {
    engine,
    info,
    root,
    generation: opened.generation,
    generationDir: opened.generationDir,
    /** One engine step over the bytes a connection delivered so far. */
    request (bytes) {
      const answer = engine.callBlobIO('storeServeRequest', [handle], bytes)
      return { envelope: answer.envelope, bytes: answer.bytes }
    },
    /** Report the outcome of an append the engine asked for. */
    commit (pending, outcome) {
      const answer = engine.callBlobIO('storeServeCommit', [handle, pending, outcome],
        new Uint8Array(0))
      return { envelope: answer.envelope, bytes: answer.bytes }
    },
    /** Perform the append an `append` envelope names; the outcome text. */
    append (envelope, bytes) {
      const path = joinPath(opened.generationDir, requireChildName(envelope.key, 'append key'))
      try {
        return appendSyncAtSize(path, bytes, envelope.expectedSize)
          ? 'ok'
          : `${envelope.key} did not have ${envelope.expectedSize} bytes; another writer changed it`
      } catch (error) {
        return error && error.message ? error.message : String(error)
      }
    },
    close () {
      try { engine.call('storeServeClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}

/** The bytes of a 500 response for a failure of this host. */
function hostFailure (message) {
  const body = new TextEncoder().encode(`factoidal serve: ${message}\n`)
  const head = new TextEncoder().encode(
    'HTTP/1.1 500 Internal Server Error\r\n' +
    'content-type: text/plain; charset=utf-8\r\n' +
    `content-length: ${body.length}\r\n` +
    'connection: close\r\n\r\n')
  return concatenate([head, body])
}

/**
 * Serve one connection: accumulate bytes, and every time the engine can
 * answer, write its answer and drop the bytes it consumed.
 */
function serveConnection (served, socket, onError) {
  let buffered = new Uint8Array(0)
  let waitFor = 0
  let finished = false

  function fail (error) {
    onError(error)
    finished = true
    socket.end(hostFailure(error && error.message ? error.message : String(error)))
  }

  function pump () {
    while (!finished && buffered.length > 0 && buffered.length >= waitFor) {
      let answer
      try {
        answer = served.request(buffered)
      } catch (error) {
        fail(error)
        return
      }
      const envelope = answer.envelope
      if (envelope.state === 'incomplete') {
        waitFor = typeof envelope.need === 'number' ? envelope.need : buffered.length + 1
        return
      }
      waitFor = 0
      let out = answer.bytes
      if (envelope.state === 'append') {
        const outcome = served.append(envelope, answer.bytes)
        try {
          out = served.commit(envelope.pending, outcome).bytes
        } catch (error) {
          fail(error)
          return
        }
      }
      socket.write(out)
      buffered = buffered.subarray(envelope.consumed)
      if (envelope.close === true) {
        finished = true
        socket.end()
        return
      }
    }
  }

  socket.on('data', (chunk) => {
    if (finished) return
    buffered = buffered.length === 0 ? new Uint8Array(chunk) : concatenate([buffered, chunk])
    pump()
  })
  socket.on('error', (error) => { finished = true; onError(error) })
}

/**
 * Start serving a collection. Resolves once the socket is bound and the
 * store is open, so a module without the ops, or a collection the engine
 * refuses, is reported by the call that started the server.
 *
 * @param {string} root the collection root
 * @param {object} [options] as `openServedStore`, plus `port`, `host`,
 *   `onError`
 * @returns {Promise<{server: object, served: object, port: number,
 *                    origin: string, close: Function}>}
 */
export async function listen (root, options = {}) {
  const net = await import('node:net')
  const served = await openServedStore(root, options)
  const onError = typeof options.onError === 'function'
    ? options.onError
    : (error) => { console.error(`factoidal serve: ${error && error.message ? error.message : error}`) }
  const sockets = new Set()
  const server = net.createServer((socket) => {
    sockets.add(socket)
    socket.on('close', () => sockets.delete(socket))
    serveConnection(served, socket, onError)
  })
  const port = typeof options.port === 'number' ? options.port : 0
  const host = typeof options.host === 'string' ? options.host : '127.0.0.1'
  await new Promise((resolve, reject) => {
    server.once('error', reject)
    server.listen(port, host, resolve)
  })
  const bound = server.address()
  const origin = `http://${host.indexOf(':') >= 0 ? `[${host}]` : host}:${bound.port}`
  return {
    server,
    served,
    port: bound.port,
    origin,
    close () {
      return new Promise((resolve) => {
        server.close(() => {
          served.close()
          resolve()
        })
        // A persistent connection would hold the server open; end them.
        for (const socket of sockets) socket.destroy()
      })
    }
  }
}

/**
 * `listen` on a worker thread with a raised call stack, which a large
 * collection needs (`bin/store-worker-host.mjs` measured `storeQueryPlan`
 * alone overflowing Node's default stack on 3,286 blocks). The engine, the
 * served store and the sockets all live on the worker; this thread only
 * starts and stops it.
 *
 * @param {string} root
 * @param {object} options as `listen`, without `engine` and `onError`
 * @returns {Promise<{origin: string, port: number, info: object,
 *                    close: Function}>}
 */
export async function listenOnWorker (root, options = {}) {
  const { Worker } = await import('node:worker_threads')
  const { workerStackMb } = await import('./pack-host.mjs')
  const worker = new Worker(new URL('./serve-worker.mjs', import.meta.url), {
    workerData: { root, options },
    resourceLimits: { stackSizeMb: workerStackMb() }
  })
  const started = await new Promise((resolve, reject) => {
    worker.once('message', resolve)
    worker.once('error', reject)
  })
  if (started.kind !== 'listening') {
    await worker.terminate()
    throw new ServeHostError(started.message, { unknownOp: started.unknownOp === true })
  }
  return {
    origin: started.origin,
    port: started.port,
    info: started.info,
    worker,
    close () {
      return new Promise((resolve) => {
        worker.once('message', () => { worker.terminate().then(() => resolve()) })
        worker.postMessage({ kind: 'close' })
      })
    }
  }
}
