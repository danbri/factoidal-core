// test/xmpp-inpage.test.mjs — the Lean XMPP server with no network
// (xmpp/inpage.mjs over the engine's message carrier, xmppMsg*): two
// clients, one of them through the WebSocket-shaped class an RFC 7395
// client such as Strophe.js uses, sign in, join a MUC room and talk.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { loadEngine } from '../bin/engine.mjs'
import { openInPageXmppServer, inPageWebSocket } from '../xmpp/inpage.mjs'

const DOMAIN = 'foafos.local'
const ROOMS = 'rooms.foafos.local'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_MUC = 'http://jabber.org/protocol/muc'
const ACCOUNTS = [{ username: 'shell', password: 's3cret' }, { username: 'watcher', password: 'w4tch' }]

const engine = await loadEngine()
const carrier = (() => { try { engine.call('xmppMsgClose', ['none']); return true } catch (e) { return !/unknown op/.test(String(e.message)) } })()
const skip = carrier ? false : 'the loaded engine has no message carrier (rebuild the wasm)'

const open = `<open xmlns='${NS_FRAMING}' to='${DOMAIN}' version='1.0'/>`
const plain = (u, p) => `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` + btoa(`\0${u}\0${p}`) + '</auth>'

/** A client over any `{send, onmessage}` pair. */
function client (send) {
  const got = []
  const waiters = []
  return {
    got,
    push (m) { got.push(m); for (const w of waiters.splice(0)) w() },
    send,
    async next (pred, ms = 5000) {
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
async function signIn (c, user, pw, resource) {
  c.send(open)
  await c.next((m) => m.includes('<stream:features'))
  c.send(plain(user, pw))
  const r = await c.next((m) => m.startsWith('<success') || m.startsWith('<failure'))
  if (!r.startsWith('<success')) return false
  c.send(open)
  await c.next((m) => m.includes('<stream:features'))
  c.send(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>${resource}</resource></bind></iq>`)
  await c.next((m) => m.includes('<jid>'))
  return true
}

test('two in-page clients, one through the WebSocket shape, talk in a MUC room', { skip }, async () => {
  const server = await openInPageXmppServer({ engine, domain: DOMAIN, mucDomain: ROOMS, accounts: ACCOUNTS, onError: () => {} })
  try {
    const link = server.connect()
    const a = client((m) => link.send(m))
    link.onmessage = (m) => a.push(m)
    assert.ok(await signIn(a, 'shell', 's3cret', 'tab1'))

    const WS = inPageWebSocket(server)
    const ws = new WS('xmpp-inpage:', 'xmpp')
    const b = client((m) => ws.send(m))
    ws.addEventListener('message', (e) => b.push(e.data))
    await new Promise((resolve) => { ws.onopen = resolve })
    assert.equal(ws.protocol, 'xmpp')
    assert.ok(await signIn(b, 'watcher', 'w4tch', 'gajim'))

    a.send(`<presence to='bus@${ROOMS}/shell'><x xmlns='${NS_MUC}'/></presence>`)
    await a.next((m) => m.includes('<presence') && m.includes(`bus@${ROOMS}/shell`))
    b.send(`<presence to='bus@${ROOMS}/watcher'><x xmlns='${NS_MUC}'/></presence>`)
    await b.next((m) => m.includes('<presence') && m.includes(`bus@${ROOMS}/watcher`) && m.includes('110'))

    a.send(`<message to='bus@${ROOMS}' type='groupchat' id='e1'><body>audio.play {"track":3}</body></message>`)
    const m = await b.next((x) => x.includes('id="e1"') || x.includes("id='e1'"))
    assert.match(m, /audio\.play/)
    assert.match(m, new RegExp(`from=["']bus@${ROOMS.replace(/\./g, '\\.')}/shell["']`))

    // The shell's tab goes away: the watcher sees it leave the room.
    link.close()
    const gone = await b.next((x) => x.includes(`bus@${ROOMS}/shell`) && x.includes('unavailable'))
    assert.match(gone, /unavailable/)
    assert.deepEqual(server.sessions().map((s) => s.full), [`watcher@${DOMAIN}/gajim`])
    ws.close()
  } finally { server.close() }
})

test('a wrong password is refused, and a closed connection takes no more messages', { skip }, async () => {
  const server = await openInPageXmppServer({ engine, domain: DOMAIN, accounts: ACCOUNTS, onError: () => {} })
  try {
    const link = server.connect()
    const a = client((m) => link.send(m))
    link.onmessage = (m) => a.push(m)
    assert.equal(await signIn(a, 'shell', 'wrong', 'x'), false)
    link.close()
    assert.equal(link.open, false)
    assert.throws(() => link.send(open), /closed/)
  } finally { server.close() }
})

test('the WebSocket shape refuses a subprotocol other than xmpp', { skip }, async () => {
  const server = await openInPageXmppServer({ engine, domain: DOMAIN, accounts: ACCOUNTS, onError: () => {} })
  try {
    const ws = new (inPageWebSocket(server))('xmpp-inpage:', 'mqtt')
    const code = await new Promise((resolve) => { ws.onclose = (e) => resolve(e.code) })
    assert.equal(code, 1006)
  } finally { server.close() }
})
