// Host lifecycle/IO controls. The mock engine supplies decisions; this suite
// makes no XMPP or Wasm conformance claim and needs no compiled artifacts.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import { EventEmitter } from 'node:events'
import net from 'node:net'
import fs from 'node:fs/promises'
import { syncBuiltinESMExports } from 'node:module'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { setImmediate as tick } from 'node:timers/promises'
import { createXmppServer } from '../xmpp/server.mjs'

test('XMPP server is available through its documented package export', async () => {
  const exported = await import('@factoidal/core/xmpp/server')
  assert.equal(exported.createXmppServer, createXmppServer)
})

function engine (feed = () => ({})) {
  const state = { opened: 0, closed: 0, sessions: new Set(), released: [], roster: '' }
  return { state, call (op, args) {
    switch (op) {
      case 'xmppOpen': state.opened++; return { handle: 'server', domain: 'example.test' }
      case 'xmppClose': state.closed++; state.sessions.clear(); return {}
      case 'xmppSessionOpen': {
        const handle = `session${state.sessions.size + 1}`
        state.sessions.add(handle)
        return { handle }
      }
      case 'xmppSessionClose':
        state.released.push(args[0]); state.sessions.delete(args[0]); return { send: [] }
      case 'xmppSessionFeed': return { send: [], route: [], presence: [], rostersSaved: [],
        close: false, bare: null, full: null, bufferedBytes: 0, ...feed(args[1]) }
      case 'xmppRosterGet': return { encoded: state.roster }
      case 'xmppRosterSet': return {}
      default: throw new Error(`unexpected mock operation: ${op}`)
    }
  } }
}

class Socket extends EventEmitter {
  destroyed = false
  writes = []
  write (text) { this.writes.push(text); return true }
  end () {}
  destroy () {
    if (!this.destroyed) {
      this.destroyed = true
      queueMicrotask(() => this.emit('close'))
    }
  }
}

async function connection (t, mock, options = {}) {
  const errors = []
  const host = await createXmppServer({ engine: mock, pollMs: 0,
    onError: error => errors.push(error), ...options })
  t.after(() => host.close())
  const socket = new Socket()
  host.server.emit('connection', socket)
  return { host, socket, errors }
}

test('XMPP host releases a session exactly once after a feed exception', async t => {
  const mock = engine(() => { throw new Error('feed failed') })
  const { host, socket, errors } = await connection(t, mock)
  socket.emit('data', Buffer.from('input'))
  await tick()
  assert.equal(socket.destroyed, true)
  assert.deepEqual(mock.state.released, ['session1'])
  assert.equal(mock.state.sessions.size, 0)
  assert.equal(host.sessions().length, 0)
  assert.equal(errors.length, 1)
})

test('XMPP host does not infer buffered input from absence of output', async t => {
  const mock = engine(() => ({ bufferedBytes: 0 }))
  const { socket, errors } = await connection(t, mock, { maxBuffered: 8 })
  for (let i = 0; i < 4; i++) socket.emit('data', Buffer.from('consumed input'))
  assert.equal(socket.destroyed, false)
  assert.deepEqual(errors, [])
})

test('XMPP host limits the residual input even when the engine also sends a reply', async t => {
  const mock = engine(() => ({ send: ['reply'], bufferedBytes: 64 }))
  const { socket, errors } = await connection(t, mock, { maxBuffered: 8 })
  socket.emit('data', Buffer.from('reply-trigger plus partial suffix'))
  await tick()
  assert.equal(socket.destroyed, true)
  assert.deepEqual(mock.state.released, ['session1'])
  assert.match(errors[0].message, /buffered bytes/)
})

test('XMPP host refuses an engine lacking the residual-buffer contract', async t => {
  const mock = engine(() => ({ bufferedBytes: undefined }))
  const { socket, errors } = await connection(t, mock)
  socket.emit('data', Buffer.from('input'))
  await tick()
  assert.equal(socket.destroyed, true)
  assert.deepEqual(mock.state.released, ['session1'])
  assert.match(errors[0].message, /bufferedBytes/)
})

test('XMPP host rejects a partial TLS configuration before opening an engine server', async () => {
  for (const config of [{ cert: 'certificate' }, { key: 'private-key' }]) {
    const mock = engine()
    await assert.rejects(createXmppServer({ engine: mock, ...config }), /cert.*key/)
    assert.equal(mock.state.opened, 0)
  }
})

test('XMPP host releases its engine server when TLS setup fails', async () => {
  const mock = engine()
  await assert.rejects(createXmppServer({ engine: mock, cert: 'invalid PEM', key: 'invalid PEM' }))
  assert.equal(mock.state.opened, 1)
  assert.equal(mock.state.closed, 1)
})

test('XMPP host closes a TCP peer that has not started its TLS handshake', { timeout: 5000 }, async () => {
  const mock = engine()
  // No TLS handshake occurs: an empty certificate chain suffices to construct
  // this transport-only control without a private-key fixture or openssl.
  const host = await createXmppServer({ engine: mock, cert: [], key: [], pollMs: 0 })
  let socket, closing, timer
  try {
    await new Promise((resolve, reject) => {
      host.server.once('error', reject)
      host.server.listen(0, '127.0.0.1', resolve)
    })
    const accepted = new Promise(resolve => host.server.once('connection', resolve))
    socket = net.connect(host.server.address().port, '127.0.0.1')
    await Promise.all([accepted, new Promise((resolve, reject) => {
      socket.once('connect', resolve)
      socket.once('error', reject)
    })])
    assert.equal(mock.state.sessions.size, 0, 'TLS must precede any engine session')
    closing = host.close()
    await Promise.race([closing, new Promise((_, reject) => {
      timer = setTimeout(() => reject(new Error('shutdown waited on an idle TLS peer')), 1000)
    })])
    assert.equal(mock.state.closed, 1)
  } finally {
    clearTimeout(timer)
    socket?.destroy()
    await (closing || host.close())
  }
})

test('XMPP host releases its engine server when state-directory initialization fails', async t => {
  const dir = await fs.mkdtemp(join(tmpdir(), 'xmpp-host-'))
  t.after(() => fs.rm(dir, { recursive: true, force: true }))
  const file = join(dir, 'file')
  await fs.writeFile(file, 'not a directory')
  const mock = engine()
  await assert.rejects(createXmppServer({ engine: mock, dir: file, accounts: [] }))
  assert.equal(mock.state.opened, 1)
  assert.equal(mock.state.closed, 1)
})

test('XMPP host serializes roster snapshots and waits for persistence before closing', { timeout: 10000 }, async () => {
  const dir = await fs.mkdtemp(join(tmpdir(), 'xmpp-host-roster-'))
  const mock = engine(() => ({ rostersSaved: ['a@example.test'] }))
  const host = await createXmppServer({ engine: mock, dir, accounts: [], pollMs: 0 })
  const socket = new Socket()
  host.server.emit('connection', socket)
  const original = fs.writeFile
  const releases = []
  const snapshots = []
  let secondWriteStarted
  const secondWrite = new Promise(resolve => { secondWriteStarted = resolve })
  // Hold the first actual file write. A second write must not overtake it.
  fs.writeFile = async (path, data, ...args) => {
    snapshots.push(data)
    if (snapshots.length === 2) secondWriteStarted()
    await new Promise(resolve => releases.push(resolve))
    return original(path, data, ...args)
  }
  syncBuiltinESMExports()
  let closing
  try {
    mock.state.roster = 'first snapshot'
    socket.emit('data', Buffer.from('first'))
    await tick()
    mock.state.roster = 'latest snapshot'
    socket.emit('data', Buffer.from('second'))
    await tick()
    assert.deepEqual(snapshots, ['first snapshot'])
    let closed = false
    closing = host.close().then(() => { closed = true })
    await tick()
    assert.equal(closed, false)
    assert.equal(mock.state.closed, 0)
    releases.shift()()
    await secondWrite
    assert.deepEqual(snapshots, ['first snapshot', 'latest snapshot'])
    releases.shift()()
    await closing
    assert.equal(await fs.readFile(join(dir, 'roster', 'a%40example.test.tsv'), 'utf8'), 'latest snapshot')
    assert.equal(mock.state.closed, 1)
    await host.close()
    assert.equal(mock.state.closed, 1)
  } finally {
    // Restore the real filesystem before cleanup, including a failed assertion.
    fs.writeFile = original
    syncBuiltinESMExports()
    for (const release of releases.splice(0)) release()
    await (closing || host.close())
    await fs.rm(dir, { recursive: true, force: true })
  }
})
