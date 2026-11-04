// test/lws-maxbody.test.mjs — the largest content of one write (issue
// https://github.com/danbri/factoidal/issues/1240). The engine refuses content over `maxBody`
// with 413 and changes nothing (L4Factoidal/LWS/Operations.lean, step_tooLarge); the HTTP host
// refuses it before reading it into memory.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import http from 'node:http'

const { openLwsStorage, listen } = await import('../lws/server.mjs')
const BASE = 'https://pod.invalid/'

test('in-process: over the limit is 413 and nothing is stored; at the limit it is stored', async () => {
  const s = await openLwsStorage({ baseIri: BASE, insecureNoAuth: true, realClock: true, maxBody: 1024 })
  try {
    const over = await s.step({ method: 'PUT', target: '/big.bin', headers: [['Content-Type', 'application/octet-stream']], body: new Uint8Array(1025) })
    assert.equal(over.status, 413)
    assert.equal((await s.step({ method: 'GET', target: '/big.bin', headers: [], body: new Uint8Array(0) })).status, 404)
    const at = await s.step({ method: 'PUT', target: '/ok.bin', headers: [['Content-Type', 'application/octet-stream']], body: new Uint8Array(1024) })
    assert.ok(at.status === 201 || at.status === 204, `PUT at the limit: ${at.status}`)
  } finally { s.close() }
})

test('the default limit is 16 MiB', async () => {
  const s = await openLwsStorage({ baseIri: BASE, insecureNoAuth: true, realClock: true })
  try {
    const over = await s.step({ method: 'PUT', target: '/big.bin', headers: [['Content-Type', 'application/octet-stream']], body: new Uint8Array(16 * 1024 * 1024 + 1) })
    assert.equal(over.status, 413)
  } finally { s.close() }
})

function request (port, { method, path, headers, chunks }) {
  return new Promise((resolve, reject) => {
    const req = http.request({ host: '127.0.0.1', port, method, path, headers }, (res) => {
      let body = ''
      res.on('data', (d) => { body += d })
      res.on('end', () => resolve({ status: res.statusCode, body }))
    })
    req.on('error', reject)
    for (const c of chunks) req.write(c)
    req.end()
  })
}

test('over HTTP: a declared Content-Length over the limit, and a chunked body over it, are 413', async () => {
  const running = await listen({ insecureNoAuth: true, realClock: true, maxBody: 1024, port: 0 })
  try {
    const declared = await request(running.port, { method: 'PUT', path: '/a.bin',
      headers: { 'content-type': 'application/octet-stream', 'content-length': '5000' }, chunks: [Buffer.alloc(5000)] })
      .catch((e) => ({ status: 'reset', body: e.message }))
    assert.ok(declared.status === 413 || declared.status === 'reset', `declared: ${declared.status}`)
    const chunked = await request(running.port, { method: 'PUT', path: '/b.bin',
      headers: { 'content-type': 'application/octet-stream', 'transfer-encoding': 'chunked' },
      chunks: [Buffer.alloc(600), Buffer.alloc(600)] }).catch((e) => ({ status: 'reset', body: e.message }))
    assert.ok(chunked.status === 413 || chunked.status === 'reset', `chunked: ${chunked.status}`)
    const small = await request(running.port, { method: 'PUT', path: '/c.bin',
      headers: { 'content-type': 'application/octet-stream', 'content-length': '10' }, chunks: [Buffer.alloc(10)] })
    assert.ok(small.status === 201 || small.status === 204, `small: ${small.status}`)
  } finally { await running.close() }
})
