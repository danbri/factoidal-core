// test/xmpp-iq-routing.test.mjs — IQ routing in the Node XMPP host, against the Lean engine.
//
// An IQ get or set is never held (L4Factoidal.XMPP.Server `handleIq_no_route`):
//   * to a full JID: delivered to that one session, or bounced service-unavailable
//     (RFC 6120 section 10.5.3.2) — https://github.com/danbri/factoidal/issues/1234;
//   * to another resource of the same account: delivered (issue 1139);
//   * to the bare JID of another account: answered by the server (RFC 6121 8.5.2.1.3);
//   * an IQ result goes to the one full JID it names, never to every session.
// The clients use RFC 7395 over Node's own WebSocket (the same engine path as TCP).

import { test } from 'node:test'
import assert from 'node:assert/strict'

const DOMAIN = 'example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }, { username: 'romeo', password: 'juli3t' }]

const serverModule = await import('../xmpp/server.mjs')
const plain = (user, pw) =>
  `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` + Buffer.from(`\0${user}\0${pw}`).toString('base64') + '</auth>'
const open = `<open xmlns='${NS_FRAMING}' to='${DOMAIN}' version='1.0'/>`

function wsClient (url) {
  const ws = new WebSocket(url, 'xmpp')
  const got = []
  const waiters = []
  ws.addEventListener('message', (e) => { got.push(String(e.data)); for (const w of waiters.splice(0)) w() })
  return {
    ws,
    got,
    opened: new Promise((resolve, reject) => { ws.addEventListener('open', resolve); ws.addEventListener('error', reject) }),
    send (t) { ws.send(t) },
    async next (pred, ms = 10000) {
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
  c.send(open)
  await c.next((m) => m.startsWith('<stream:features'))
  c.send(plain(user, pw))
  await c.next((m) => m.startsWith('<success'))
  c.send(open)
  await c.next((m) => m.startsWith('<stream:features'))
  c.send(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>${resource}</resource></bind></iq>`)
  await c.next((m) => m.includes('<jid>'))
  return c
}

async function start () {
  return serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
    websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
}

const version = (id, to, type = 'get') => `<iq type='${type}' id='${id}' to='${to}'><query xmlns='jabber:iq:version'/></iq>`

test('an IQ to a full JID reaches that one session, and its result comes back to the sender only', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    const romeo2 = await bound(server.wsOrigin, 'romeo', 'juli3t', 'garden')
    juliet.send(version('v1', `romeo@${DOMAIN}/orchard`))
    const req = await romeo.next((m) => m.includes("id=\"v1\"") || m.includes("id='v1'"))
    assert.match(req, /from="juliet@example\.com\/balcony"/)
    romeo.send(`<iq type='result' id='v1' to='juliet@${DOMAIN}/balcony'/>`)
    const res = await juliet.next((m) => /id="v1"/.test(m))
    assert.match(res, /type="result"/)
    // The other resource of romeo saw neither.
    await new Promise((r) => setTimeout(r, 300))
    assert.ok(!romeo2.got.some((m) => /v1/.test(m)), `romeo/garden received ${JSON.stringify(romeo2.got)}`)
    for (const c of [juliet, romeo, romeo2]) c.ws.close()
  } finally { await server.close() }
})

test('an IQ to a full JID with no session is bounced service-unavailable at once (issue 1234)', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    const t0 = Date.now()
    juliet.send(version('v2', `romeo@${DOMAIN}/orchard`))
    const err = await juliet.next((m) => /id="v2"/.test(m), 3000)
    assert.match(err, /type="error"/)
    assert.match(err, /service-unavailable/)
    assert.match(err, /from="romeo@example\.com\/orchard"/)
    assert.ok(Date.now() - t0 < 3000)
    // And after romeo goes away: the pod-offline case.
    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    romeo.ws.close()
    await new Promise((r) => setTimeout(r, 300))
    juliet.send(version('v3', `romeo@${DOMAIN}/orchard`))
    assert.match(await juliet.next((m) => /id="v3"/.test(m), 3000), /service-unavailable/)
    juliet.ws.close()
  } finally { await server.close() }
})

test('an IQ result to a full JID with no session is dropped, never bounced', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    juliet.send(`<iq type='result' id='r1' to='romeo@${DOMAIN}/orchard'/>`)
    await new Promise((r) => setTimeout(r, 500))
    assert.ok(!juliet.got.some((m) => /r1/.test(m)), JSON.stringify(juliet.got))
    juliet.ws.close()
  } finally { await server.close() }
})

test('two resources of one account reach each other (issue 1139)', async () => {
  const server = await start()
  try {
    const t = await bound(server.wsOrigin, 'juliet', 'r0m30', 't')
    const u = await bound(server.wsOrigin, 'juliet', 'r0m30', 'u')
    u.send(version('same1', `juliet@${DOMAIN}/t`))
    assert.match(await t.next((m) => /id="same1"/.test(m)), /from="juliet@example\.com\/u"/)
    t.ws.close(); u.ws.close()
  } finally { await server.close() }
})

test('an IQ to the bare JID of another account is answered by the server', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    juliet.send(version('v4', `romeo@${DOMAIN}`))
    assert.match(await juliet.next((m) => /id="v4"/.test(m)), /service-unavailable/)
    await new Promise((r) => setTimeout(r, 300))
    assert.ok(!romeo.got.some((m) => /v4/.test(m)), 'the bare-JID IQ must not reach a resource')
    juliet.ws.close(); romeo.ws.close()
  } finally { await server.close() }
})
