// SPARQL over an SBM11 generation, in Node and in the browser, through the
// wasm ops sbm11Open / sbm11Query / sbm11Close
// (formal/lean4/Wasm/Ops/Sbm11.lean; https://github.com/danbri/factoidal/issues/1009 KR1).
//
// WHAT THIS FILE IS ALLOWED TO DO
// Move bytes. The engine asks for (source, file, offset, length) through the
// bridge globalThis.__factoidalReadAt, and for the size of a file through
// globalThis.__factoidalFileSize (the EM_JS bodies in
// formal/lean4/ffi/l4_hostread.c call them synchronously). This file finds
// the reader that serves `source` and answers. It never reads a manifest,
// checks a length or a digest, or decides which file a query needs: the
// engine names every file and checks every answer against the manifest
// (formal/lean4/L4Factoidal/Storage/Sbm11/HostSession.lean). Iron rule 7.
//
// READERS
// A reader is { readAt(file, offset, length) -> Uint8Array, size(file) ->
// number | null }, both synchronous: the engine is inside WebAssembly and
// cannot wait for a promise. Node: lib/sbm11-node.mjs reads a directory with
// fs. A browser worker: a reader over OPFS FileSystemSyncAccessHandle
// (stage 4 of https://github.com/danbri/factoidal/issues/1007). A caller
// registers a reader under a source name; a source with no registered reader
// goes to the default reader (Node: the directory of that name).

const readers = new Map()
let defaultReader = null
let bridgeInstalled = false

function readerFor (source) {
  const r = readers.get(source)
  if (r) return r
  if (defaultReader) return defaultReader(source)
  return null
}

function installBridge () {
  if (bridgeInstalled) return
  bridgeInstalled = true
  // A thrown error and a wrong length both reach Lean as "the host gave no
  // bytes"; the engine then refuses the read with the file name.
  globalThis.__factoidalReadAt = (source, file, offset, length) => {
    const r = readerFor(source)
    if (!r) return null
    return r.readAt(file, offset, length)
  }
  globalThis.__factoidalFileSize = (source, file) => {
    const r = readerFor(source)
    if (!r) return null
    return r.size(file)
  }
}

/**
 * Serve `source` with `reader` ({ readAt(file, offset, length), size(file) },
 * both synchronous). `null` removes the registration.
 */
export function registerSbm11Source (source, reader) {
  installBridge()
  if (reader === null) { readers.delete(String(source)); return }
  if (!reader || typeof reader.readAt !== 'function' || typeof reader.size !== 'function') {
    throw new TypeError('registerSbm11Source: reader needs readAt(file, offset, length) and size(file)')
  }
  readers.set(String(source), reader)
}

/** The reader for a source with no registration: `(source) => reader | null`. */
export function setDefaultSbm11Reader (factory) {
  installBridge()
  defaultReader = factory
}

function envelope (raw) {
  const j = typeof raw === 'string' ? JSON.parse(raw) : raw
  if (!j || j.ok !== true) {
    const e = new Error((j && j.error) || 'sbm11: unknown error')
    e.code = 'SBM11'
    throw e
  }
  return j
}

/**
 * The SBM11 functions over an engine loader: `loadEngine()` resolves to the
 * engine handle (`call(op, args)`).
 */
export function sbm11Api (loadEngine) {
  /**
   * Open an SBM11 generation (a generation directory, or a collection root
   * whose CURRENT file names one). Returns { generation, terms, query(sparql,
   * options), close() }. `query` answers { path, rows, format, result, json }:
   * `result` is the text `l4sbm11 query` writes (SPARQL JSON for SELECT and
   * ASK, N-Triples for CONSTRUCT and DESCRIBE), `json` its parse for
   * SELECT and ASK.
   */
  async function openSbm11 (source, options = {}) {
    installBridge()
    if (options.reader) registerSbm11Source(source, options.reader)
    const eng = await loadEngine()
    const opened = envelope(eng.call('sbm11Open', [String(source)]))
    const handle = opened.handle
    let open = true
    return {
      handle,
      generation: opened.generation,
      terms: Number(opened.terms),
      query (sparql, qopts = {}) {
        if (!open) throw new Error('sbm11: the store is closed')
        const o = {}
        if (qopts.base != null) o.base = String(qopts.base)
        if (qopts.sparql12) o.sparql12 = true
        if (qopts.reference) o.reference = true
        const args = [handle, String(sparql), JSON.stringify(o)]
        // The byte-region entry returns the result bytes outside the
        // envelope; a large answer is then not escaped into a JSON string
        // and parsed again (Wasm/Ops/Sbm11.lean sbm11QueryBlob).
        let j, bytes
        if (typeof eng.callBlobIO === 'function') {
          const answer = eng.callBlobIO('sbm11Query', args, new Uint8Array(0))
          j = envelope(answer.envelope)
          bytes = answer.bytes
        } else {
          j = envelope(eng.call('sbm11Query', args))
        }
        let text = bytes === undefined ? j.result : undefined
        return {
          path: j.path,
          rows: Number(j.rows),
          format: j.format,
          bytesRead: Number(j.bytesRead),
          reads: Number(j.reads),
          /** the answer as bytes (UTF-8) */
          get bytes () { return bytes ?? new TextEncoder().encode(text) },
          /** the answer as text */
          get result () {
            if (text === undefined) text = new TextDecoder().decode(bytes)
            return text
          },
          get json () { return j.format === 'srj' ? JSON.parse(this.result) : undefined }
        }
      },
      close () {
        if (!open) return
        open = false
        envelope(eng.call('sbm11Close', [handle]))
      }
    }
  }
  return { openSbm11 }
}
