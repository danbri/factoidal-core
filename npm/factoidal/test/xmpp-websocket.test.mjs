// test/xmpp-websocket.test.mjs — XMPP over WebSocket (RFC 7395 over
// RFC 6455) in the Node XMPP host, against the Lean engine in wasm.
//
// Every decision is Lean: `HTTP.WebSocket.upgrade` (handshake, Origin,
// subprotocol), `HTTP.WebSocket.decode` / `Reader` (frames),
// `XMPP.WebSocket.unitOfMessage` / `messageOfSend` (RFC 7395 framing),
// `Server.step` (XMPP), and `Wasm/Ops/XmppSession.lean` `wsFeedPure`. The
// cases use Node's own WebSocket client (an independent RFC 6455
// implementation) and raw sockets for what a well-behaved client never
// sends.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'

const DOMAIN = 'example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }, { username: 'romeo', password: 'juli3t' }]

const serverModule = await import('../xmpp/server.mjs')

const plain = (user, pw) =>
  `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` + Buffer.from(`\0${user}\0${pw}`).toString('base64') + '</auth>'
const open = `<open xmlns='${NS_FRAMING}' to='${DOMAIN}' version='1.0'/>`

async function start (websocket) {
  return serverModule.listen({
    domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
    websocket: { port: 0, path: '/xmpp-websocket', ...websocket }
  })
}

/** A WebSocket client that collects text messages. */
function wsClient (url) {
  const ws = new WebSocket(url, 'xmpp')
  const got = []
  const waiters = []
  ws.addEventListener('message', (e) => { got.push(String(e.data)); for (const w of waiters.splice(0)) w() })
  return {
    ws,
    got,
    opened: new Promise((resolve, reject) => { ws.addEventListener('open', resolve); ws.addEventListener('error', reject) }),
    closed: new Promise((resolve) => ws.addEventListener('close', resolve)),
    send (t) { ws.send(t) },
    async next (pred, ms = 15000) {
      const t0 = Date.now()
      for (;;) {
        const i = got.findIndex(pred)
        if (i >= 0) return got.splice(0, i + 1)[i]
        if (Date.now() - t0 > ms) throw new Error(`timed out; got ${JSON.stringify(got)}`)
        await new Promise((resolve) => { waiters.push(resolve); setTimeout(resolve, 50) })
      }
    }
  }
}

async function bound (url, user, pw, resource) {
  const c = wsClient(url)
  await c.opened
  assert.equal(c.ws.protocol, 'xmpp')
  c.send(open)
  const header = await c.next((m) => m.startsWith('<open'))
  assert.match(header, new RegExp(`xmlns='${NS_FRAMING}'`))
  const features = await c.next((m) => m.startsWith('<stream:features'))
  assert.match(features, /xmlns:stream='http:\/\/etherx\.jabber\.org\/streams'/)
  assert.match(features, /SCRAM-SHA-256/)
  c.send(plain(user, pw))
  await c.next((m) => m.startsWith('<success'))
  c.send(open)
  await c.next((m) => m.startsWith('<stream:features'))
  c.send(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>${resource}</resource></bind></iq>`)
  const bind = await c.next((m) => m.includes('<jid>'))
  assert.ok(bind.includes(`${user}@${DOMAIN}/${resource}`))
  return c
}

/** Send a raw HTTP request; resolve with everything received until close. */
function rawRequest (port, text, after) {
  return new Promise((resolve, reject) => {
    const s = net.connect(port, '127.0.0.1')
    const chunks = []
    s.on('data', (d) => {
      chunks.push(d)
      if (after && Buffer.concat(chunks).includes('\r\n\r\n')) { s.write(after); after = null }
    })
    s.on('close', () => resolve(Buffer.concat(chunks)))
    s.on('error', reject)
    s.write(text)
    setTimeout(() => s.destroy(), 5000)
  })
}

const handshake = (extra = '', path = '/xmpp-websocket', protocol = 'xmpp') =>
  `GET ${path} HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n` +
  'Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n' +
  `Sec-WebSocket-Protocol: ${protocol}\r\n${extra}\r\n`

test('websocket: two clients log in over RFC 7395 and exchange messages', async () => {
  const server = await start({ allowNoOrigin: true })
  try {
    assert.match(server.wsOrigin, /^ws:\/\/127\.0\.0\.1:\d+\/xmpp-websocket$/)
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    juliet.send(`<message to='romeo@${DOMAIN}' type='chat' from='mallory@evil.example'><body>hi &amp; bye</body></message>`)
    const m = await romeo.next((x) => x.startsWith('<message'))
    assert.match(m, /hi &amp; bye/)
    // The server stamps `from` (RFC 6120 section 8.1.2.1); the claimed one is gone.
    assert.match(m, /from="juliet@example\.com\/balcony"/)
    assert.ok(!m.includes('mallory'))
    juliet.send(`<close xmlns='${NS_FRAMING}'/>`)
    await juliet.next((x) => x.startsWith('<close'))
    await juliet.closed
    romeo.ws.close()
  } finally { await server.close() }
})

test('websocket: the accept key, and an Origin, path or subprotocol not allowed', async () => {
  const server = await start({ allowedOrigins: ['https://app.example'] })
  try {
    const port = server.wsServer.address().port
    const ok = (await rawRequest(port, handshake('Origin: https://app.example\r\n'))).toString()
    assert.match(ok, /^HTTP\/1\.1 101 /)
    // RFC 6455 section 1.3's example key and accept value.
    assert.match(ok, /Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK\+xOo=/)
    assert.match((await rawRequest(port, handshake('Origin: https://evil.example\r\n'))).toString(), /^HTTP\/1\.1 403 /)
    assert.match((await rawRequest(port, handshake())).toString(), /^HTTP\/1\.1 403 /)
    assert.match((await rawRequest(port, handshake('Origin: https://app.example\r\n', '/other'))).toString(), /^HTTP\/1\.1 404 /)
    assert.match((await rawRequest(port, handshake('Origin: https://app.example\r\n', '/xmpp-websocket', 'chat'))).toString(), /^HTTP\/1\.1 400 /)
  } finally { await server.close() }
})

test('websocket: an unmasked client frame is closed with 1002 (RFC 6455 section 5.1)', async () => {
  const server = await start({ allowNoOrigin: true })
  try {
    const port = server.wsServer.address().port
    const text = Buffer.from(open)
    const unmasked = Buffer.concat([Buffer.from([0x81, text.length]), text])
    const reply = await rawRequest(port, handshake(), unmasked)
    const at = reply.indexOf('\r\n\r\n') + 4
    assert.match(reply.subarray(0, at).toString(), /^HTTP\/1\.1 101 /)
    const frame = reply.subarray(at)
    // A close frame (opcode 8) with status 1002, and no <open/> answer.
    assert.equal(frame[0], 0x88)
    assert.equal(frame.readUInt16BE(2), 1002)
    assert.ok(!reply.includes('<open'))
  } finally { await server.close() }
})
