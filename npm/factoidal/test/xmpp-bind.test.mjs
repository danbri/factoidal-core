// test/xmpp-bind.test.mjs — RFC 6120 section 7.7.2.2: a live session keeps its full JID, and a client
// that asks for that resource gets a server-generated one, on every transport. The engine's proofs
// are `Server.resourceFor_free`, `Server.step_fullStep` and, in Wasm/Ops/XmppSession.lean,
// `Unique.nodup`, `drain_unique`, `wsFeedPure_unique` and `msgFeedPure_unique`.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { execFile } from 'node:child_process'
import { mkdtemp, readFile, rm } from 'node:fs/promises'
import net from 'node:net'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import tls from 'node:tls'
import { promisify } from 'node:util'
import { loadEngine } from '../bin/engine.mjs'
import { listen, openXmppServer } from '../xmpp/server.mjs'
import { openInPageXmppServer } from '../xmpp/inpage.mjs'

const DOMAIN = 'example.com'
const MUC = 'conference.example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_MUC = 'http://jabber.org/protocol/muc'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }, { username: 'romeo', password: 'juli3t' }]
const PHONE = `juliet@${DOMAIN}/phone`

const plain = (user, pw) =>
  `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` + Buffer.from(`\0${user}\0${pw}`).toString('base64') + '</auth>'
const bindIq = (resource) => `<iq type='set' id='b1'><bind xmlns='${NS_BIND}'>` +
  (resource === null ? '' : `<resource>${resource}</resource>`) + '</bind></iq>'
const jidOf = (text) => /<jid>([^<]+)<\/jid>/.exec(text)?.[1]

/** Texts arrive through `push`; `next` takes the first that matches, and what came before it. */
function inbox (send) {
  const got = []
  const waiters = []
  return {
    send,
    got,
    push (m) { got.push(m); for (const w of waiters.splice(0)) w() },
    async next (pred, ms = 10000) {
      const t0 = Date.now()
      for (;;) {
        const i = got.findIndex(pred)
        if (i >= 0) return got.splice(0, i + 1)[i]
        if (Date.now() - t0 > ms) throw new Error(`timed out; got ${JSON.stringify(got)}`)
        await new Promise((resolve) => { waiters.push(resolve); setTimeout(resolve, 20) })
      }
    }
  }
}

/** SASL and bind on a client; the client's `jid` is the one in the bind result. */
async function signIn (c, open, user, pw, resource) {
  const features = (m) => m.includes('</stream:features>') || m.includes('<stream:features')
  c.send(open)
  await c.next(features)
  c.send(plain(user, pw))
  await c.next((m) => m.includes('<success'))
  c.send(open)
  await c.next(features)
  c.send(bindIq(resource))
  c.jid = jidOf(await c.next((m) => m.includes('<jid>')))
  return c
}

const streamOpen = `<stream:stream xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' to='${DOMAIN}' version='1.0'>`
const framedOpen = `<open xmlns='${NS_FRAMING}' to='${DOMAIN}' version='1.0'/>`

/** A byte-stream client: each read is one text, which is enough for these short exchanges. */
function streamClient (socket) {
  const c = inbox((t) => socket.write(t))
  socket.setEncoding('utf8')
  socket.on('data', (t) => c.push(t))
  socket.on('error', () => {})
  c.quit = () => socket.destroy()
  return c
}

function wsClient (url) {
  const ws = new WebSocket(url, 'xmpp')
  const c = inbox((t) => ws.send(t))
  ws.addEventListener('message', (e) => c.push(String(e.data)))
  c.ready = new Promise((resolve, reject) => { ws.addEventListener('open', resolve); ws.addEventListener('error', reject) })
  c.quit = () => ws.close()
  return c
}

function pageClient (server) {
  const link = server.connect()
  const c = inbox((t) => link.send(t))
  link.onmessage = (m) => c.push(m)
  c.quit = () => link.close()
  return c
}

async function until (check) {
  for (let i = 0; i < 250; i++) {
    if (check()) return
    await new Promise((resolve) => setTimeout(resolve, 20))
  }
  assert.fail('the condition did not come true')
}

/**
 * The same checks on any transport. `connect` gives a signed-in client.
 * Two live clients ask for one resource: the second gets another one, and each is reached alone.
 * When the first goes, the resource is free again.
 */
async function conflictChecks (connect, sessions) {
  const first = await connect('juliet', 'r0m30', 'phone')
  assert.equal(first.jid, PHONE)
  const second = await connect('juliet', 'r0m30', 'phone')
  assert.notEqual(second.jid, PHONE)
  assert.ok(second.jid.startsWith(`juliet@${DOMAIN}/`))
  assert.notEqual(second.jid, `juliet@${DOMAIN}/`)
  assert.deepEqual(sessions().map((s) => s.full).filter((f) => f.startsWith('juliet')).sort(), [PHONE, second.jid].sort())

  const romeo = await connect('romeo', 'juli3t', 'orchard')
  // An IQ to a full JID goes to that one session (a message goes to every resource of the account).
  const iq = (to, id) => `<iq to='${to}' type='get' id='${id}'><query xmlns='urn:example:bind'/></iq>`
  romeo.send(iq(PHONE, 'to-first'))
  await first.next((m) => m.includes('to-first'))
  romeo.send(iq(second.jid, 'to-second'))
  await second.next((m) => m.includes('to-second'))
  assert.ok(!second.got.some((m) => m.includes('to-first')))
  assert.ok(!first.got.some((m) => m.includes('to-second')))

  first.quit()
  await until(() => !sessions().some((s) => s.full === PHONE))
  const third = await connect('juliet', 'r0m30', 'phone')
  assert.equal(third.jid, PHONE)
  second.quit(); third.quit(); romeo.quit()
}

async function makeCert () {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-bind-'))
  await promisify(execFile)('openssl', ['req', '-x509', '-newkey', 'rsa:2048', '-nodes', '-days', '1', '-subj', `/CN=${DOMAIN}`,
    '-keyout', join(dir, 'key.pem'), '-out', join(dir, 'cert.pem')])
  return { dir, cert: await readFile(join(dir, 'cert.pem')), key: await readFile(join(dir, 'key.pem')) }
}

test('bind: TCP: a held resource goes to the new client as a new one, and comes free with its session', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {} })
  try {
    await conflictChecks((u, p, r) => signIn(streamClient(net.connect(s.port, '127.0.0.1')), streamOpen, u, p, r), s.sessions)
  } finally { await s.close() }
})

test('bind: direct TLS: the same', async () => {
  const cert = await makeCert()
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, startTls: true, directTlsPort: 0, cert: cert.cert, key: cert.key, pollMs: 0, onError: () => {} })
  try {
    const port = Number(new URL(s.directOrigin.replace('xmpps:', 'http:')).port)
    await conflictChecks(async (u, p, r) => {
      const socket = tls.connect({ port, host: '127.0.0.1', rejectUnauthorized: false })
      await new Promise((resolve, reject) => { socket.once('secureConnect', resolve); socket.once('error', reject) })
      return signIn(streamClient(socket), streamOpen, u, p, r)
    }, s.sessions)
  } finally {
    await s.close()
    await rm(cert.dir, { recursive: true, force: true })
  }
})

test('bind: WebSocket: the same', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
  try {
    await conflictChecks(async (u, p, r) => {
      const c = wsClient(s.wsOrigin)
      await c.ready
      return signIn(c, framedOpen, u, p, r)
    }, s.sessions)
  } finally { await s.close() }
})

test('bind: in-page server: the same', async () => {
  const s = await openInPageXmppServer({ engine: await loadEngine(), domain: DOMAIN, accounts: ACCOUNTS, onError: () => {} })
  try {
    await conflictChecks((u, p, r) => signIn(pageClient(s), framedOpen, u, p, r), s.sessions)
  } finally { s.close() }
})

test('bind: across transports: a WebSocket client meets a TCP client on one resource', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
  try {
    const tcp = await signIn(streamClient(net.connect(s.port, '127.0.0.1')), streamOpen, 'juliet', 'r0m30', 'phone')
    const ws = wsClient(s.wsOrigin)
    await ws.ready
    await signIn(ws, framedOpen, 'juliet', 'r0m30', 'phone')
    assert.equal(tcp.jid, PHONE)
    assert.notEqual(ws.jid, PHONE)
    tcp.quit(); ws.quit()
  } finally { await s.close() }
})

test('bind: another account may hold the same resource name', async () => {
  const s = await listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {} })
  try {
    const j = await signIn(streamClient(net.connect(s.port, '127.0.0.1')), streamOpen, 'juliet', 'r0m30', 'phone')
    const r = await signIn(streamClient(net.connect(s.port, '127.0.0.1')), streamOpen, 'romeo', 'juli3t', 'phone')
    assert.equal(j.jid, PHONE)
    assert.equal(r.jid, `romeo@${DOMAIN}/phone`)
    j.quit(); r.quit()
  } finally { await s.close() }
})

test('bind: a client that binds another stream\'s id still gets a free resource', async () => {
  const opened = await openXmppServer({ domain: DOMAIN, accounts: ACCOUNTS })
  try {
    const feed = (session, text) => session.feed(text)
    const toBind = (session) => {
      feed(session, streamOpen)
      feed(session, plain('juliet', 'r0m30'))
      feed(session, streamOpen)
    }
    const a = opened.openSession({ streamId: 'stream-a' })
    const b = opened.openSession({ streamId: 'stream-b' })
    toBind(a)
    toBind(b)
    assert.equal(feed(a, bindIq('stream-b')).full, `juliet@${DOMAIN}/stream-b`)
    const full = feed(b, bindIq(null)).full
    assert.notEqual(full, `juliet@${DOMAIN}/stream-b`)
    assert.ok(full.startsWith(`juliet@${DOMAIN}/stream-b`))
    a.close(); b.close()
  } finally { opened.close() }
})

test('bind: a stream that ended holds nothing, even before the host closes its handle; that close takes no seat from the new session', async () => {
  const opened = await openXmppServer({ domain: DOMAIN, accounts: ACCOUNTS, mucDomain: MUC })
  try {
    const up = (streamId, user, pw, resource) => {
      const session = opened.openSession({ streamId })
      session.feed(streamOpen)
      session.feed(plain(user, pw))
      session.feed(streamOpen)
      const answer = session.feed(bindIq(resource))
      return { session, full: answer.full }
    }
    const join = (c, nick) => c.session.feed(`<presence to='seat@${MUC}/${nick}'><x xmlns='${NS_MUC}'/></presence>`)
    const old = up('s1', 'juliet', 'r0m30', 'phone')
    const romeo = up('s2', 'romeo', 'juli3t', 'orchard')
    join(old, 'jul')
    join(romeo, 'rom')

    // The old stream ends: the room hears at once, with the handle still open.
    const ended = old.session.feed('</stream:stream>')
    assert.equal(ended.full, null)
    assert.ok(ended.routeFull.some((r) => r.to === romeo.full && r.text.includes(`seat@${MUC}/jul`) && r.text.includes('unavailable')))

    const fresh = up('s3', 'juliet', 'r0m30', 'phone')
    assert.equal(fresh.full, PHONE)
    join(fresh, 'jul')

    // The host closes the old handle now: the seat is the new session's, and it stays.
    assert.deepEqual(old.session.close().routeFull, [])
    const said = romeo.session.feed(`<message to='seat@${MUC}' type='groupchat' id='g'><body>hi</body></message>`)
    assert.ok(said.routeFull.some((r) => r.to === PHONE && r.text.includes('hi')))

    // A connection lost with no stream end goes when the host closes it.
    const left = fresh.session.close()
    assert.ok(left.routeFull.some((r) => r.to === romeo.full && r.text.includes('unavailable')))
    assert.equal(up('s4', 'juliet', 'r0m30', 'phone').full, PHONE)
  } finally { opened.close() }
})
