// test/xmpp-ping.test.mjs — a dead connection sends no FIN, so the server asks. A bound session that
// is silent gets a ping (XEP-0199 on TCP, an RFC 6455 ping frame on a WebSocket), any byte counts as
// the answer, and a session that stays silent is closed, which frees its resource for the client
// when it comes back. The engine's side is `Server.Session.ping` and `Session.ping_isSome`.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { createHash, randomBytes } from 'node:crypto'
import net from 'node:net'
import { listen, openXmppServer } from '../xmpp/server.mjs'

const DOMAIN = 'example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }]
const PHONE = `juliet@${DOMAIN}/phone`
const FAST = { pingIntervalMs: 150, pingTimeoutMs: 200 }
const WS = { port: 0, path: '/xmpp-websocket', allowNoOrigin: true }

const plain = `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` + Buffer.from('\0juliet\0r0m30').toString('base64') + '</auth>'
const bindIq = `<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>phone</resource></bind></iq>`
const streamOpen = `<stream:stream xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' to='${DOMAIN}' version='1.0'>`
const framedOpen = `<open xmlns='${NS_FRAMING}' to='${DOMAIN}' version='1.0'/>`
const isPing = (m) => m.includes('urn:xmpp:ping')
const pause = (ms) => new Promise((resolve) => setTimeout(resolve, ms))

/** The peer sees the close first, so the server's side may be a moment behind it. */
async function released (s) {
  for (let i = 0; i < 100; i++) {
    if (!s.sessions().some((x) => x.full === PHONE)) return
    await pause(10)
  }
  assert.fail('the session still holds its resource')
}

function inbox (send) {
  const got = []
  return {
    send,
    got,
    push (m) { got.push(m) },
    async next (pred, ms = 5000) {
      const t0 = Date.now()
      for (;;) {
        const i = got.findIndex(pred)
        if (i >= 0) return got.splice(0, i + 1)[i]
        if (Date.now() - t0 > ms) throw new Error(`timed out; got ${JSON.stringify(got)}`)
        await pause(5)
      }
    }
  }
}

async function signIn (c, open, bind = true) {
  const features = (m) => m.includes('<stream:features')
  c.send(open)
  await c.next(features)
  c.send(plain)
  await c.next((m) => m.includes('<success'))
  c.send(open)
  await c.next(features)
  if (!bind) return c
  c.send(bindIq)
  c.jid = /<jid>([^<]+)<\/jid>/.exec(await c.next((m) => m.includes('<jid>')))[1]
  return c
}

function tcpClient (port) {
  const socket = net.connect(port, '127.0.0.1')
  const c = inbox((t) => socket.write(t))
  socket.setEncoding('utf8')
  socket.on('data', (t) => c.push(t))
  socket.on('error', () => {})
  c.closed = new Promise((resolve) => socket.once('close', resolve))
  c.quit = () => socket.destroy()
  return c
}

/** A WebSocket client that reads frames and never answers a ping, as a dead peer would not. The
 *  global WebSocket answers by itself, so this case needs the frames by hand. */
async function silentWsClient (url) {
  const { port } = new URL(url)
  const socket = net.connect(Number(port), '127.0.0.1')
  const c = inbox((t) => {
    const body = Buffer.from(t, 'utf8')
    const key = randomBytes(4)
    const head = body.length < 126
      ? Buffer.from([0x81, 0x80 | body.length])
      : Buffer.from([0x81, 0x80 | 126, body.length >> 8, body.length & 255])
    socket.write(Buffer.concat([head, key, body.map((b, i) => b ^ key[i % 4])]))
  })
  c.frames = []
  let buf = Buffer.alloc(0)
  let upgraded = false
  await new Promise((resolve, reject) => {
    socket.on('error', reject)
    socket.on('data', (chunk) => {
      buf = Buffer.concat([buf, chunk])
      if (!upgraded) {
        const end = buf.indexOf('\r\n\r\n')
        if (end < 0) return
        assert.match(buf.subarray(0, end).toString(), /^HTTP\/1.1 101/)
        buf = buf.subarray(end + 4)
        upgraded = true
        resolve()
      }
      for (;;) {
        if (buf.length < 2) return
        let length = buf[1] & 127
        let start = 2
        if (length === 126) {
          if (buf.length < 4) return
          length = buf.readUInt16BE(2)
          start = 4
        }
        if (buf.length < start + length) return
        const op = buf[0] & 15
        c.frames.push(op)
        if (op === 1) c.push(buf.subarray(start, start + length).toString('utf8'))
        buf = buf.subarray(start + length)
      }
    })
    socket.write(`GET /xmpp-websocket HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n` +
      `Sec-WebSocket-Key: ${randomBytes(16).toString('base64')}\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Protocol: xmpp\r\n\r\n`)
  })
  socket.removeAllListeners('error')
  socket.on('error', () => {})
  c.closed = new Promise((resolve) => socket.once('close', resolve))
  c.quit = () => socket.destroy()
  return c
}

test('ping: TCP: a silent session is pinged and closed, and the client gets its resource back', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, ...FAST })
  try {
    const dead = await signIn(tcpClient(s.port), streamOpen)
    assert.equal(dead.jid, PHONE)
    const ping = await dead.next(isPing)
    assert.match(ping, /type="get"/)
    assert.ok(ping.includes(`to="${PHONE}"`) && ping.includes(`from="${DOMAIN}"`), ping)
    await dead.closed
    await released(s)
    const back = await signIn(tcpClient(s.port), streamOpen)
    assert.equal(back.jid, PHONE)
    back.quit()
  } finally { await s.close() }
})

test('ping: TCP: a client that answers stays, with a result or with service-unavailable', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, ...FAST })
  try {
    for (const answer of [
      (id) => `<iq type='result' id='${id}' to='${DOMAIN}'/>`,
      (id) => `<iq type='error' id='${id}' to='${DOMAIN}'><error type='cancel'><service-unavailable xmlns='urn:ietf:params:xml:ns:xmpp-stanzas'/></error></iq>`
    ]) {
      const c = await signIn(tcpClient(s.port), streamOpen)
      const ids = new Set()
      for (let i = 0; i < 3; i++) {
        const ping = await c.next(isPing)
        const id = /id="([^"]+)"/.exec(ping)[1]
        ids.add(id)
        c.send(answer(id))
      }
      assert.equal(ids.size, 3)
      assert.ok(s.sessions().some((x) => x.full === PHONE))
      // The server says nothing back to an answer.
      assert.deepEqual(c.got.filter((m) => !isPing(m)), [])
      c.quit()
      for (let i = 0; i < 100 && s.sessions().length > 0; i++) await pause(10)
    }
  } finally { await s.close() }
})

test('ping: any byte counts as the answer, and traffic means no ping at all', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, ...FAST })
  try {
    const c = await signIn(tcpClient(s.port), streamOpen)
    for (let i = 0; i < 12; i++) { c.send(' '); await pause(50) }
    assert.ok(!c.got.some(isPing))
    await c.next(isPing)
    c.send(' ')
    await pause(100)
    assert.ok(s.sessions().some((x) => x.full === PHONE))
    c.quit()
  } finally { await s.close() }
})

test('ping: WebSocket: the client layer answers a ping frame, with no XMPP stanza', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, websocket: WS, ...FAST })
  try {
    const ws = new WebSocket(s.wsOrigin, 'xmpp')
    const c = inbox((t) => ws.send(t))
    ws.addEventListener('message', (e) => c.push(String(e.data)))
    await new Promise((resolve, reject) => { ws.addEventListener('open', resolve); ws.addEventListener('error', reject) })
    await signIn(c, framedOpen)
    await pause(800)
    assert.ok(s.sessions().some((x) => x.full === PHONE))
    assert.ok(!c.got.some(isPing))
    ws.close()
  } finally { await s.close() }
})

test('ping: WebSocket: a peer that does not answer the frame is closed', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, websocket: WS, ...FAST })
  try {
    const dead = await signIn(await silentWsClient(s.wsOrigin), framedOpen)
    assert.equal(dead.jid, PHONE)
    await dead.closed
    assert.ok(dead.frames.includes(9), `frames: ${dead.frames}`)
    await released(s)
  } finally { await s.close() }
})

test('ping: a session with no resource is not pinged; the login timeout is for that', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, loginTimeoutMs: 0, ...FAST })
  try {
    const c = await signIn(tcpClient(s.port), streamOpen, false)
    let closed = false
    c.closed.then(() => { closed = true })
    await pause(600)
    assert.ok(!c.got.some(isPing))
    assert.equal(closed, false)
    c.quit()
  } finally { await s.close() }
})

test('ping: an interval of 0 turns pings off', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, pingIntervalMs: 0 })
  try {
    const c = await signIn(tcpClient(s.port), streamOpen)
    await pause(300)
    assert.ok(!c.got.some(isPing))
    assert.ok(s.sessions().some((x) => x.full === PHONE))
    c.quit()
  } finally { await s.close() }
})

test('ping: a timeout of 0 with pings on is refused', async () => {
  await assert.rejects(listen({ domain: DOMAIN, accounts: ACCOUNTS, pingTimeoutMs: 0 }), /pingTimeoutMs must be positive/)
})

test('ping: the op refuses a session that is not bound', async () => {
  const opened = await openXmppServer({ domain: DOMAIN, accounts: ACCOUNTS })
  try {
    const session = opened.openSession({})
    assert.deepEqual({ sent: session.ping('p1').sent, send: session.ping('p1').send }, { sent: false, send: [] })
    session.close()
  } finally { opened.close() }
})
