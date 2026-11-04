// factoidal/lws/inpage.mjs — one Lean LWS storage with no network: it runs
// in the page (or a worker, or Node) beside the code that uses it, and is
// reached through a `fetch`-shaped function.
//
//   import { loadEngine } from '@factoidal/core/browser'
//   import { openInPageLwsStorage } from '@factoidal/core/lws/inpage'
//   const pod = await openInPageLwsStorage({ engine: await loadEngine(),
//     baseIri: 'https://pod.foafos.local/', principal: 'urn:foafos:shell',
//     rootAcl, storageKey, snapshot: saved,
//     onSnapshot: (s) => save(s) })
//   const r = await pod.fetch('https://pod.foafos.local/notes/a.txt', { method: 'PUT', body: 'hi' })
//
// The storage has a component principal (issue 1238): every request is that
// agent's, no token is read, and Web Access Control still decides it
// (L4Factoidal/LWS/Authorization.lean). Whoever holds the object can use it,
// so the host page decides which code gets it, as with xmpp/inpage.mjs.
//
// It is kept as one snapshot (`lwsSnapshot`), which the engine seals when a
// `storageKey` is given. After each step that changed the storage this file
// asks the engine for the snapshot and gives it to `onSnapshot`; the caller
// keeps it (IndexedDB, a file) and passes it back as `snapshot` to reopen.
// The engine checks that snapshot and refuses one sealed under another key.
//
// The engine makes every protocol decision (status, headers, bodies). This
// file turns a fetch call into the request record of the wasm ABI
// (docs/lws-solid-conformance.md, "wasm ABI") and the response record into a
// Response. Notifications are off: there is no network to deliver them on.
// No Node API; `crypto.getRandomValues`, `Request` and `Response` only.

/** Random bytes for the engine, base64 (see lws/server.mjs, entropyBase64). */
function entropyBase64 (size = 32) {
  const bytes = new Uint8Array(size)
  globalThis.crypto.getRandomValues(bytes)
  let text = ''
  for (const b of bytes) text += String.fromCharCode(b)
  return btoa(text)
}

function handleOf (envelope) {
  if (envelope === null || typeof envelope !== 'object') return null
  for (const name of ['handle', 'id']) {
    const value = envelope[name]
    if (typeof value === 'string' && value.length > 0) return value
    if (typeof value === 'number') return String(value)
  }
  return null
}

/**
 * @param {object} options
 * @param {object} options.engine a loaded engine handle (`loadEngine()`), with callBlobIO
 * @param {string} options.baseIri the absolute IRI the storage root maps to; fetch
 *   reaches only IRIs under it
 * @param {string} options.principal the component principal (an IRI); every request is its
 * @param {string} [options.rootAcl] the root ACL (Turtle) of a new storage
 * @param {string} [options.owner] the WebID the storage advertises
 * @param {string} [options.storageKey] key text (64 hex digits or base64url); seals the snapshot
 * @param {object} [options.snapshot] a snapshot to continue from (from onSnapshot)
 * @param {function} [options.onSnapshot] (snapshot) => void, after each change
 * @param {number} [options.maxBody] the largest content of one write (the engine's default otherwise)
 * @returns {Promise<{fetch: Function, snapshot: Function, close: Function, baseIri: string}>}
 */
export async function openInPageLwsStorage (options = {}) {
  const { engine } = options
  if (!engine || typeof engine.callBlobIO !== 'function') throw new TypeError('openInPageLwsStorage: an engine with callBlobIO is required')
  if (typeof options.baseIri !== 'string') throw new TypeError('openInPageLwsStorage: baseIri is required')
  if (typeof options.principal !== 'string') throw new TypeError('openInPageLwsStorage: principal is required')
  const base = new URL(options.baseIri)
  const config = { baseIri: base.href, principal: options.principal, notifications: false, entropy: entropyBase64() }
  for (const name of ['rootAcl', 'owner', 'storageKey']) {
    if (typeof options[name] === 'string') config[name] = options[name]
  }
  if (typeof options.maxBody === 'number') config.maxBody = options.maxBody
  if (options.snapshot !== undefined && options.snapshot !== null) config.snapshot = options.snapshot
  const opened = engine.call('lwsOpen', [JSON.stringify(config)])
  const handle = handleOf(opened)
  if (handle === null) throw new Error('lwsOpen answered with no handle')
  const onSnapshot = typeof options.onSnapshot === 'function' ? options.onSnapshot : null
  let closed = false

  const snapshot = () => {
    const answer = engine.call('lwsSnapshot', [handle, JSON.stringify({ nonce: entropyBase64(12) })])
    if (answer === null || typeof answer !== 'object' || answer.snapshot === undefined) {
      throw new Error('lwsSnapshot answered with no snapshot')
    }
    return answer.snapshot
  }

  /** A fetch to this storage: the same arguments as `fetch`, a real Response back. */
  async function podFetch (input, init) {
    if (closed) throw new TypeError('this storage is closed')
    const request = new Request(input, init)
    const url = new URL(request.url)
    if (url.origin !== base.origin || !url.pathname.startsWith(base.pathname)) {
      throw new TypeError('the IRI is not in this storage')
    }
    const target = '/' + url.pathname.slice(base.pathname.length) + url.search
    const content = request.method === 'GET' || request.method === 'HEAD'
      ? new Uint8Array(0)
      : new Uint8Array(await request.arrayBuffer())
    const record = {
      method: request.method,
      target,
      headers: [...request.headers],
      now: Math.floor(Date.now() / 1000),
      random: entropyBase64(16)
    }
    const got = engine.callBlobIO('lwsStep', [handle, JSON.stringify(record)], content)
    const envelope = got.envelope
    if (envelope === null || typeof envelope !== 'object') throw new Error('lwsStep answered with no envelope')
    // A storage with a component principal and no files has nothing to
    // fetch, resolve or read; an engine that asks is not one this host runs.
    for (const ask of ['fetch', 'resolve', 'read']) {
      if (envelope[ask] !== undefined && envelope[ask] !== null) throw new Error(`lwsStep asked this host to ${ask}, which an in-page storage cannot`)
    }
    const answer = (envelope.response !== null && typeof envelope.response === 'object') ? envelope.response : envelope
    if (typeof answer.status !== 'number') throw new Error('lwsStep answered with no status in its response record')
    if (envelope.changed === true && onSnapshot !== null) onSnapshot(snapshot())
    const headers = new Headers()
    for (const [name, value] of Array.isArray(answer.headers) ? answer.headers : []) headers.append(name, value)
    // No content is a null body: a Response refuses an empty one with 204 or 304.
    const body = got.bytes instanceof Uint8Array && got.bytes.length > 0 ? got.bytes : null
    return new Response(body, { status: answer.status, headers })
  }

  return {
    baseIri: base.href,
    fetch: podFetch,
    snapshot,
    close () {
      closed = true
      try { engine.call('lwsClose', [handle]) } catch (_error) { /* already gone */ }
    }
  }
}
