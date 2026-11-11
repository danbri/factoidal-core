// test/xmpp-proxy-protocol.test.mjs — `xmpp-serve --proxy-protocol` and the
// failed-login limit on client address tags.
//
// The PROXY protocol v2 header (HAProxy's spec, section 2.2) is decided by the
// engine (`proxyHeaderParse`, formal/lean4/L4Factoidal/Net/ProxyProtocol.lean);
// the host only buffers bytes. The headers below are test input, written by
// hand from the spec. The limit keys on an HMAC-SHA-256 tag of the address
// (`addressTag`, formal/lean4/L4Factoidal/Net/LoginLimit.lean); no log line may
// hold an address.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import tls from 'node:tls'
import { once } from 'node:events'
import { execFileSync, spawn } from 'node:child_process'
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { createXmppServer, xmppServerOpsAvailable } from '../xmpp/server.mjs'
import { loadEngine } from '../bin/engine.mjs'

const engine = await loadEngine()
const { available } = await xmppServerOpsAvailable({ engine })
let parseOp = false
try { engine.callBlobIO('proxyHeaderParse', [], new Uint8Array(0)); parseOp = true } catch (_error) { /* older engine */ }
const skip = !available ? 'the engine has no XMPP server ops' : !parseOp ? 'the engine has no proxyHeaderParse' : false

const DOMAIN = 'localhost'
const ACCOUNTS = [{ username: 'alice', password: 'alice-pw' }, { username: 'bob', password: 'bob-pw' }]
const HEADER = `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`
const SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const plain = (user, pw) => `<auth xmlns='${SASL}' mechanism='PLAIN'>${Buffer.from(`\0${user}\0${pw}`).toString('base64')}</auth>`

const SIGNATURE = Buffer.from([0x0D, 0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54, 0x0A])
const A = '203.0.113.7'
const B = '198.51.100.9'
const C = '192.0.2.44'

function v2 (command, family, block) {
  const fixed = Buffer.from([0x20 | command, family, block.length >> 8, block.length & 0xff])
  return Buffer.concat([SIGNATURE, fixed, block])
}
const v4 = (ip, port = 50000) => v2(1, 0x11, Buffer.from([...ip.split('.').map(Number), 10, 0, 0, 1, port >> 8, port & 0xff, 0x14, 0x66]))
function v6 (groups, port = 50000) {
  const block = Buffer.alloc(36)
  groups.forEach((g, i) => block.writeUInt16BE(g, i * 2))
  block.writeUInt16BE(port, 32); block.writeUInt16BE(5222, 34)
  return v2(1, 0x21, block)
}
const local = () => v2(0, 0x00, Buffer.alloc(0))

const logs = []
async function start (options = {}, spy = engine) {
  const host = await createXmppServer({
    domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, engine: spy,
    onError: (e) => logs.push(e.message), onLog: (l) => logs.push(l), ...options
  })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  return { host, port: host.server.address().port }
}

/** A client over a socket: collect text, wait for a word or for the end. */
function client (socket) {
  const c = { socket, text: '', ended: false }
  socket.on('data', (d) => { c.text += d.toString('utf8') })
  socket.on('close', () => { c.ended = true })
  socket.on('error', () => { c.ended = true })
  c.until = async (word, ms = 3000) => {
    const end = Date.now() + ms
    while (!c.text.includes(word) && Date.now() < end) await sleep(5)
    assert.ok(c.text.includes(word), `wanted ${word}, got ${c.text.slice(-300)}`)
  }
  c.closed = async (ms = 3000) => {
    const end = Date.now() + ms
    while (!c.ended && Date.now() < end) await sleep(5)
    assert.equal(c.ended, true, 'the server closed the connection')
  }
  return c
}

async function connect (port, ...chunks) {
  const socket = net.connect(port, '127.0.0.1')
  await once(socket, 'connect')
  const c = client(socket)
  for (const chunk of chunks) socket.write(chunk)
  return c
}

/** One failed PLAIN login for `user` from `header`'s address, on a new stream. */
async function attempt (port, header, user, pw) {
  const c = await connect(port, Buffer.concat([header, Buffer.from(HEADER + plain(user, pw))]))
  await c.until('</failure>')
  const m = /<failure[^>]*>\s*<([a-z-]+)/.exec(c.text)
  c.socket.destroy()
  return m && m[1]
}

async function login (port, header, user, pw) {
  const c = await connect(port, Buffer.concat([header, Buffer.from(HEADER + plain(user, pw))]))
  const end = Date.now() + 3000
  while (!/<success|<\/failure>/.test(c.text) && Date.now() < end) await sleep(5)
  c.socket.destroy()
  if (c.text.includes('<success')) return 'success'
  const m = /<failure[^>]*>\s*<([a-z-]+)/.exec(c.text)
  return m ? m[1] : 'no answer'
}

test('IPv4 PROXY header and the stream header in one write: the stream opens', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const c = await connect(port, Buffer.concat([v4(A), Buffer.from(HEADER)]))
    await c.until('</stream:features>')
    c.socket.destroy()
  } finally { await host.close() }
})

test('IPv6 PROXY header: the stream opens', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const c = await connect(port, Buffer.concat([v6([0x2001, 0xdb8, 1, 2, 3, 4, 5, 6]), Buffer.from(HEADER)]))
    await c.until('</stream:features>')
    c.socket.destroy()
  } finally { await host.close() }
})

test('LOCAL header (a health check of the proxy): the stream opens', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const c = await connect(port, Buffer.concat([local(), Buffer.from(HEADER)]))
    await c.until('</stream:features>')
    c.socket.destroy()
  } finally { await host.close() }
})

test('the header split over several TCP writes: the stream opens', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const bytes = Buffer.concat([v4(A), Buffer.from(HEADER)])
    const c = await connect(port)
    c.socket.setNoDelay(true)
    for (const cut of [[0, 3], [3, 12], [12, 15], [15, 20], [20, 28], [28, bytes.length]]) {
      c.socket.write(bytes.subarray(cut[0], cut[1]))
      await sleep(20)
    }
    await c.until('</stream:features>')
    c.socket.destroy()
  } finally { await host.close() }
})

test('no header (an XMPP stream header first), a bad signature, a v1 header: closed, no byte answered', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const bad = Buffer.from(v4(A)); bad[5] = 0x0E
    for (const first of [Buffer.from(HEADER), bad, Buffer.from(`PROXY TCP4 ${A} 10.0.0.1 50000 5222\r\n${HEADER}`)]) {
      const c = await connect(port, first)
      await c.closed()
      assert.equal(c.text, '')
    }
  } finally { await host.close() }
})

test('a truncated header: closed at the header timeout, no byte answered', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true, proxyHeaderTimeoutMs: 300 })
  try {
    const c = await connect(port, v4(A).subarray(0, 20))
    await sleep(100)
    assert.equal(c.ended, false)
    await c.closed(2000)
    assert.equal(c.text, '')
    assert.ok(logs.includes('closing a connection that sent no PROXY header in time'))
  } finally { await host.close() }
})

test('an oversized header length, and a PROXY length shorter than its addresses: closed', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const big = Buffer.concat([SIGNATURE, Buffer.from([0x21, 0x11, 0x10, 0x00])])
    const short = v2(1, 0x11, Buffer.alloc(8))
    for (const first of [big, short]) {
      const c = await connect(port, first)
      await c.closed()
      assert.equal(c.text, '')
    }
  } finally { await host.close() }
})

test('direct TLS: the header and the TLS ClientHello in one TCP read', { skip }, async () => {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-proxy-'))
  execFileSync('openssl', ['req', '-x509', '-newkey', 'rsa:2048', '-nodes', '-sha256', '-days', '1',
    '-subj', `/CN=${DOMAIN}`, '-keyout', join(dir, 'key.pem'), '-out', join(dir, 'cert.pem')], { stdio: 'ignore' })
  const { host, port } = await start({
    proxyProtocol: true, cert: await readFile(join(dir, 'cert.pem')), key: await readFile(join(dir, 'key.pem'))
  })
  try {
    const raw = net.connect(port, '127.0.0.1')
    await once(raw, 'connect')
    // Hold the header until the ClientHello is written, then send both at once.
    raw.cork()
    raw.write(v4(A))
    const secure = tls.connect({ socket: raw, rejectUnauthorized: false, servername: DOMAIN })
    process.nextTick(() => raw.uncork())
    await once(secure, 'secureConnect')
    const c = client(secure)
    secure.write(HEADER)
    await c.until('</stream:features>')
    secure.destroy()
  } finally {
    await host.close()
    await rm(dir, { recursive: true, force: true })
  }
})

test('WebSocket listener: the header, then the HTTP upgrade, in one write', { skip }, async () => {
  const host = await createXmppServer({
    domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, engine, proxyProtocol: true,
    onError: (e) => logs.push(e.message), onLog: (l) => logs.push(l),
    websocket: { path: '/xmpp-websocket', allowedOrigins: [], allowNoOrigin: true }
  })
  await new Promise((resolve) => host.wsServer.listen(0, '127.0.0.1', resolve))
  const port = host.wsServer.address().port
  const upgrade = 'GET /xmpp-websocket HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n' +
    'Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Protocol: xmpp\r\n\r\n'
  try {
    const c = await connect(port, Buffer.concat([v6([0x2001, 0xdb8, 9, 9, 0, 0, 0, 1]), Buffer.from(upgrade)]))
    await c.until('HTTP/1.1 101')
    c.socket.destroy()
    const d = await connect(port, Buffer.from(upgrade))
    await d.closed()
    assert.equal(d.text, '')
  } finally { await host.close() }
})

test('without the flag no header is read: the bytes go to XMPP, and proxyHeaderParse is never called', { skip }, async () => {
  const calls = []
  const spy = Object.create(engine)
  spy.callBlobIO = (op, args, bytes) => { calls.push(op); return engine.callBlobIO(op, args, bytes) }
  const { host, port } = await start({}, spy)
  try {
    const c = await connect(port, Buffer.concat([v4(A), Buffer.from(HEADER)]))
    await sleep(300)
    assert.ok(!c.text.includes('</stream:features>'), 'a header must not be skipped without the flag')
    assert.ok(!calls.includes('proxyHeaderParse'))
    c.socket.destroy()
    // A plain stream still works.
    const d = await connect(port, HEADER)
    await d.until('</stream:features>')
    d.socket.destroy()
    assert.ok(!calls.includes('proxyHeaderParse'))
  } finally { await host.close() }
})

test('5 failed logins from address A block A, not B', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    for (let i = 0; i < 5; i++) assert.equal(await attempt(port, v4(A), `nobody${i}`, 'wrong'), 'not-authorized')
    assert.equal(await login(port, v4(A), 'alice', 'alice-pw'), 'temporary-auth-failure')
    assert.equal(await login(port, v4(B), 'alice', 'alice-pw'), 'success')
  } finally { await host.close() }
})

test('IPv6: one /64 is one address for the limit', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    for (let i = 0; i < 5; i++) {
      assert.equal(await attempt(port, v6([0x2001, 0xdb8, 1, 2, 0, 0, 0, 0x10 + i]), `nobody${i}`, 'wrong'), 'not-authorized')
    }
    assert.equal(await login(port, v6([0x2001, 0xdb8, 1, 2, 0xffff, 0, 0, 1]), 'alice', 'alice-pw'), 'temporary-auth-failure')
    assert.equal(await login(port, v6([0x2001, 0xdb8, 1, 3, 0, 0, 0, 1]), 'alice', 'alice-pw'), 'success')
  } finally { await host.close() }
})

test('the per-account limit still works across addresses', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    for (let i = 0; i < 5; i++) assert.equal(await attempt(port, v4(`203.0.113.${100 + i}`), 'bob', 'wrong'), 'not-authorized')
    assert.equal(await login(port, v4(C), 'bob', 'bob-pw'), 'temporary-auth-failure')
    assert.equal(await login(port, v4(C), 'alice', 'alice-pw'), 'success')
  } finally { await host.close() }
})

test('--no-address-limit with the flag: failures from A count per account only', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true, addressLimit: false })
  try {
    for (let i = 0; i < 5; i++) assert.equal(await attempt(port, v4(A), `nobody${i}`, 'wrong'), 'not-authorized')
    assert.equal(await login(port, v4(A), 'alice', 'alice-pw'), 'success')
  } finally { await host.close() }
})

test('the log holds address tags, never an address', { skip }, async () => {
  const { host, port } = await start({ proxyProtocol: true })
  try {
    const c = await connect(port, Buffer.concat([v4(A), Buffer.from(HEADER)]))
    await c.until('</stream:features>')
    c.socket.destroy()
    const d = await connect(port, Buffer.concat([local(), Buffer.from(HEADER)]))
    await d.until('</stream:features>')
    d.socket.destroy()
  } finally { await host.close() }
  const all = logs.join('\n')
  assert.match(all, /connection from address [0-9a-f]{12}\b/)
  for (const address of [A, B, C, '127.0.0.1', '2001:db8', '::1', '203.0.113.1']) {
    assert.ok(!all.includes(address), `the log must not hold ${address}`)
  }
})

test('xmpp-serve --proxy-protocol logs each connection by address tag, never by address', { skip }, async (t) => {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-cli-proxy-'))
  await writeFile(join(dir, 'accounts'), 'alice:alice-pw\n')
  const cli = new URL('../bin/factoidal.mjs', import.meta.url).pathname
  const child = spawn(process.execPath, [cli, 'xmpp-serve', dir, '--domain', DOMAIN, '--port', '0', '--proxy-protocol'], { stdio: ['ignore', 'pipe', 'pipe'] })
  t.after(async () => { child.kill('SIGTERM'); await rm(dir, { recursive: true, force: true }) })
  let stderr = ''
  child.stderr.on('data', (d) => { stderr += d.toString('utf8') })
  const until = async (re, ms = 20000) => {
    const end = Date.now() + ms
    while (!re.test(stderr) && Date.now() < end) await sleep(20)
    const m = re.exec(stderr)
    assert.ok(m, `wanted ${re}, got ${stderr.slice(-400)}`)
    return m
  }
  const port = Number((await until(/listening on \S*:(\d+)/))[1])
  const c = await connect(port, Buffer.concat([v4(A), Buffer.from(HEADER)]))
  await c.until('</stream:features>')
  c.socket.destroy()
  const m = await until(/xmpp-serve: connection from address ([0-9a-f]{12})\b/)
  assert.ok(!stderr.includes(A), 'the address itself is never logged')
  assert.equal(m[1].length, 12)
})
