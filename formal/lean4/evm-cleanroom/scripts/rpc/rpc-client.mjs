import { createHash } from 'node:crypto'
import http from 'node:http'
import https from 'node:https'

const METHODS = new Set([
  'eth_chainId', 'eth_getBlockByNumber', 'eth_getBlockByHash', 'eth_getCode',
  'eth_call', 'eth_getTransactionByHash', 'eth_getTransactionReceipt',
])
const MAX_RESPONSE_BYTES = 4 * 1024 * 1024
const SHA256 = value => createHash('sha256').update(value).digest('hex')
export const object = value => value !== null && typeof value === 'object' && !Array.isArray(value)
export const hexData = value => typeof value === 'string' && value.startsWith('0x') &&
  value.length % 2 === 0 && /^0x[0-9a-f]*$/i.test(value)

export class CaptureError extends Error {}

function endpoint(value) {
  try {
    if (value.length > 4096) throw new Error()
    const url = new URL(value)
    if (!['http:', 'https:'].includes(url.protocol) || url.hash) throw new Error()
    const username = decodeURIComponent(url.username)
    const password = decodeURIComponent(url.password)
    if (url.username || url.password) {
      if (url.protocol !== 'https:') throw new Error()
    }
    const auth = url.username || url.password
      ? `Basic ${Buffer.from(`${username}:${password}`).toString('base64')}` : undefined
    // Paths can carry provider API keys. None of the path, query or auth is evidence.
    const pathParts = url.pathname.split('/').flatMap(part => [part, decodeURIComponent(part)])
    const rawQueryValues = url.search.slice(1).split('&').filter(part => part.includes('='))
      .map(part => part.slice(part.indexOf('=') + 1))
    const identifiers = [...new Set([url.href, url.search, url.pathname === '/' ? '' : url.pathname, ...pathParts,
      url.username, url.password, username, password, auth, ...url.searchParams.values(), ...rawQueryValues]
      .filter(Boolean))]
    if (identifiers.length > 64) throw new Error()
    url.username = ''
    url.password = ''
    return { url, auth, identifiers }
  } catch {
    throw new CaptureError('Invalid or overlong RPC URL. Use HTTP or HTTPS and HTTPS for URL credentials.')
  }
}

const containsIdentifier = (text, identifiers) => identifiers.some(identifier =>
  identifier.length >= 4 ? text.includes(identifier) : text === identifier)

function inspect(envelope, identifiers) {
  const pending = []
  for (const [key, value] of Object.entries(envelope)) {
    if (key !== 'id' && key !== 'jsonrpc') pending.push(value, key)
  }
  let privateData = false
  while (pending.length > 0) {
    const entry = pending.pop()
    if (typeof entry === 'string' || typeof entry === 'number') {
      privateData ||= containsIdentifier(String(entry), identifiers)
    } else if (JSON.isRawJSON(entry)) {
      privateData ||= containsIdentifier(entry.rawJSON, identifiers)
    } else if (Array.isArray(entry)) {
      for (const child of entry) pending.push(child)
    } else if (object(entry)) {
      for (const [key, child] of Object.entries(entry)) {
        pending.push(key, child)
      }
    }
  }
  return privateData
}

function peer(socket) {
  const address = socket.remoteAddress
  const loopback = address === '::1' || address?.startsWith('127.') || address?.startsWith('::ffff:127.')
  const details = { remoteAddress: loopback ? null : address ?? null }
  if (socket.encrypted) {
    const cipher = socket.getCipher()
    Object.assign(details, {
      tls: {
        protocol: socket.getProtocol(), cipher: cipher?.standardName ?? null,
        serverCertificateSha256: socket.getPeerCertificate()?.fingerprint256 ?? null,
        verified: socket.authorized,
      },
    })
  }
  return details
}

function post({ url, auth }, body, timeoutMs) {
  return new Promise((resolve, reject) => {
    const transport = url.protocol === 'https:' ? https : http
    const headers = {
      'content-type': 'application/json', 'content-length': Buffer.byteLength(body),
      'accept-encoding': 'identity',
    }
    const fail = reason => {
      reject(new CaptureError(reason))
      request.destroy()
    }
    const request = transport.request(url, {
      method: 'POST', headers: auth ? { ...headers, authorization: auth } : headers,
    }, response => {
      const status = response.statusCode
      if (status < 200 || status >= 300) {
        fail(`HTTP status ${status}`)
        return
      }
      const encoding = response.headers['content-encoding']
      if (encoding && encoding !== 'identity') {
        fail('Unexpected RPC response content encoding')
        return
      }
      const declared = response.headers['content-length']
      if (declared !== undefined && Number(declared) > MAX_RESPONSE_BYTES) {
        fail('RPC response byte limit exceeded')
        return
      }
      const source = peer(response.socket)
      const contentType = response.headers['content-type']?.toLowerCase()
      const responseHeaders = {
        ...(declared === undefined ? {} : { 'content-length': Number(declared) }),
        ...(['application/json', 'application/json; charset=utf-8'].includes(contentType)
          ? { 'content-type': contentType } : {}),
      }
      const chunks = []
      let bytes = 0
      response.on('data', chunk => {
        bytes += chunk.length
        if (bytes > MAX_RESPONSE_BYTES) {
          fail('RPC response byte limit exceeded')
        } else {
          chunks.push(chunk)
        }
      })
      response.on('end', () => bytes <= MAX_RESPONSE_BYTES && resolve({
        body: Buffer.concat(chunks, bytes),
        retrieval: {
          requestHeaders: headers, responseHeaders,
          httpStatus: status, bytes, ...source,
        },
      }))
      response.on('error', error => reject(error))
    })
    const timer = setTimeout(() => fail('RPC request timed out'), timeoutMs)
    request.on('error', error => reject(error))
    request.on('close', () => {
      clearTimeout(timer)
      reject(new CaptureError('RPC connection closed before a complete response'))
    })
    request.end(body)
  })
}

// JSON.parse resolves duplicate names by keeping the last. Reject those
// before parsing so that a different JSON reader sees the same assertions.
// This scans string boundaries and nesting only; JSON.parse validates syntax.
function checkJsonNames(json) {
  const containers = []
  for (let index = 0; index < json.length; index++) {
    const char = json[index]
    if (char === '{' || char === '[') {
      if (containers.length >= 64) throw new CaptureError('RPC JSON nesting limit exceeded')
      containers.push(char === '{' ? new Set() : null)
    } else if (char === '}' || char === ']') {
      containers.pop()
    } else if (char === '"') {
      const start = index
      for (index++; index < json.length; index++) {
        if (json[index] === '\\') index++
        else if (json[index] === '"') break
      }
      const names = containers.at(-1)
      if (!names) continue
      let next = index + 1
      while (json[next] === ' ' || json[next] === '\t' || json[next] === '\n' || json[next] === '\r') next++
      if (json[next] !== ':') continue
      const name = JSON.parse(json.slice(start, index + 1))
      if (names.has(name)) throw new CaptureError('Duplicate member name in RPC JSON')
      names.add(name)
    }
  }
}

export function parseUniqueJson(body) {
  try {
    const json = new TextDecoder('utf-8', { fatal: true }).decode(body)
    checkJsonNames(json)
    return JSON.parse(json, (_key, value, context) =>
      typeof value === 'number' && (!Number.isSafeInteger(value) || context.source !== String(value))
        ? JSON.rawJSON(context.source) : value)
  } catch (error) {
    if (error instanceof CaptureError) throw error
    throw new CaptureError('Malformed RPC JSON')
  }
}

function rpcError(error, privateData, identifiers) {
  if (!object(error) || !Number.isSafeInteger(error.code) || typeof error.message !== 'string') {
    throw new CaptureError('Malformed JSON-RPC error')
  }
  if (containsIdentifier(String(error.code), identifiers)) {
    throw new CaptureError('RPC error contains credential or endpoint data')
  }
  const reverts = error.code === 3 || (error.code === -32000 &&
    (error.message === 'execution reverted' || error.message.startsWith('execution reverted: ')))
  if (!privateData && reverts && hexData(error.data)) {
    return { code: error.code, revertDataHex: error.data }
  }
  return { code: error.code }
}

export function createRpc(value, timeoutMs) {
  const remote = endpoint(value)
  const requests = []
  let lastId = 0
  return {
    origin: remote.url.origin,
    requests,
    async read(method, params) {
      if (!METHODS.has(method)) throw new CaptureError('RPC method is outside the read-only allowlist')
      const id = ++lastId
      const started = new Date()
      const begin = performance.now()
      try {
        const { body, retrieval } = await post(remote, JSON.stringify({ jsonrpc: '2.0', id, method, params }), timeoutMs)
        const envelope = parseUniqueJson(body)
        if (!object(envelope) || envelope.jsonrpc !== '2.0' || envelope.id !== id ||
            Object.hasOwn(envelope, 'result') === Object.hasOwn(envelope, 'error')) {
          throw new CaptureError('Malformed JSON-RPC response envelope or mismatched id')
        }
        const privateData = inspect(envelope, remote.identifiers)
        const reply = Object.hasOwn(envelope, 'error')
          ? { error: rpcError(envelope.error, privateData, remote.identifiers) } : { result: envelope.result }
        if (privateData && Object.hasOwn(reply, 'result')) {
          throw new CaptureError('RPC result contains credential or endpoint data')
        }
        requests.push({
          id, method, params, startedAt: started.toISOString(),
          durationMs: Math.round(performance.now() - begin), ...retrieval,
          // Error messages and error data aside from strict revert bytes are untrusted.
          ...(Object.hasOwn(reply, 'result') ? { responseBodySha256: SHA256(body) } : { error: reply.error }),
        })
        return reply
      } catch (error) {
        // Keep transport causes useful without forwarding URLs, headers or provider text.
        const reason = error instanceof CaptureError ? error.message :
          (typeof error.code === 'string' && /^(?:E[A-Z0-9_]+|HPE_[A-Z0-9_]+)$/.test(error.code)
            ? `Transport error ${error.code}` : 'Transport error')
        throw new CaptureError(`${method}: ${reason}`)
      }
    },
  }
}
