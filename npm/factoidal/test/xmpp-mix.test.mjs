// test/xmpp-mix.test.mjs — XEP-0369 MIX channels, joined through the user's own server
// (XEP-0405 MIX-PAM), in the Node XMPP host against the Lean engine
// (L4Factoidal/XMPP/Mix.lean: message_recipients, message_from_sender,
// message_nonparticipant, joinChannel_bares_nodup, joinChannel_nicks_nodup,
// joinChannel_again, leaveChannel_gone). Clients speak RFC 7395 over Node's WebSocket.

import { test } from 'node:test'
import assert from 'node:assert/strict'

const DOMAIN = 'example.com'
const MIX = 'mix.example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_CORE = 'urn:xmpp:mix:core:1'
const NS_PAM = 'urn:xmpp:mix:pam:2'
const ACCOUNTS = [{ username: 'hag66', password: 'h3c4t3' }, { username: 'hecate', password: 'm00n' },
  { username: 'mallory', password: 'evil' }]

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

const start = () => serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
  mixDomain: MIX, websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
const create = (c, id, name) => c.send(`<iq type='set' id='${id}' to='${MIX}'><create xmlns='${NS_CORE}' channel='${name}'/></iq>`)
const join = (c, id, user, name, nick) => c.send(`<iq type='set' id='${id}' to='${user}@${DOMAIN}'>` +
  `<client-join xmlns='${NS_PAM}' channel='${name}@${MIX}'><join xmlns='${NS_CORE}'>` +
  `<subscribe node='urn:xmpp:mix:nodes:messages'/>${nick ? `<nick>${nick}</nick>` : ''}</join></client-join></iq>`)
const byId = (id) => (m) => m.includes(`id="${id}"`)

test('mix: the server offers MIX-PAM; create, join through PAM, message to every account', async () => {
  const server = await start()
  try {
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    hag.send(`<iq type='get' id='i1' to='hag66@${DOMAIN}'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>`)
    assert.match(await hag.next(byId('i1')), /urn:xmpp:mix:pam:2/)
    create(hag, 'c1', 'coven')
    assert.match(await hag.next(byId('c1')), /type="result"/)
    join(hag, 'j1', 'hag66', 'coven', 'third witch')
    const joined = await hag.next(byId('j1'))
    assert.match(joined, /id="p1"/)
    assert.match(joined, /<nick>third witch<\/nick>/)

    const hecate = await bound(server.wsOrigin, 'hecate', 'm00n', 'x')
    join(hecate, 'j2', 'hecate', 'coven')
    assert.match(await hecate.next(byId('j2')), /type="result"/)

    hag.send(`<message to='coven@${MIX}' type='groupchat' id='m1'><body>Harpier cries</body></message>`)
    for (const c of [hag, hecate]) {
      const m = await c.next(byId('m1'))
      assert.match(m, new RegExp(`from="coven@${MIX}"`))
      assert.match(m, /<nick>third witch<\/nick>/)
      assert.ok(!m.includes('<jid>'), `a participant's JID was disclosed: ${m}`)
    }
    hag.ws.close(); hecate.ws.close()
  } finally { await server.close() }
})

test('mix: membership is the account: an offline participant gets the message when it binds', async () => {
  const server = await start()
  try {
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    create(hag, 'c1', 'coven')
    await hag.next(byId('c1'))
    join(hag, 'j1', 'hag66', 'coven', 'third witch')
    await hag.next(byId('j1'))
    const hecate = await bound(server.wsOrigin, 'hecate', 'm00n', 'x')
    join(hecate, 'j2', 'hecate', 'coven')
    await hecate.next(byId('j2'))
    hecate.ws.close()
    await new Promise((r) => setTimeout(r, 300))
    hag.send(`<message to='coven@${MIX}' type='groupchat' id='m2'><body>while you were out</body></message>`)
    await hag.next(byId('m2'))
    const back = await bound(server.wsOrigin, 'hecate', 'm00n', 'y')
    assert.match(await back.next(byId('m2')), /while you were out/)
    hag.ws.close(); back.ws.close()
  } finally { await server.close() }
})

test('mix: an outsider cannot post; a direct join is refused; a taken nick is refused; leave', async () => {
  const server = await start()
  try {
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    create(hag, 'c1', 'coven')
    await hag.next(byId('c1'))
    join(hag, 'j1', 'hag66', 'coven', 'third witch')
    await hag.next(byId('j1'))
    const mallory = await bound(server.wsOrigin, 'mallory', 'evil', 'x')
    mallory.send(`<message to='coven@${MIX}' type='groupchat' id='s1'><body>buy now</body></message>`)
    assert.match(await mallory.next(byId('s1')), /not-acceptable/)
    mallory.send(`<iq type='set' id='d1' to='coven@${MIX}'><join xmlns='${NS_CORE}'/></iq>`)
    assert.match(await mallory.next(byId('d1')), /not-allowed/)
    join(mallory, 'j3', 'mallory', 'coven', 'third witch')
    assert.match(await mallory.next(byId('j3')), /conflict/)
    await new Promise((r) => setTimeout(r, 300))
    assert.ok(!hag.got.some((m) => /buy now/.test(m)), 'an outsider reached the channel')
    hag.send(`<iq type='set' id='l1' to='hag66@${DOMAIN}'><client-leave xmlns='${NS_PAM}' channel='coven@${MIX}'><leave xmlns='${NS_CORE}'/></client-leave></iq>`)
    assert.match(await hag.next(byId('l1')), /client-leave/)
    hag.send(`<message to='coven@${MIX}' type='groupchat' id='m3'><body>still here?</body></message>`)
    assert.match(await hag.next(byId('m3')), /not-acceptable/)
    hag.ws.close(); mallory.ws.close()
  } finally { await server.close() }
})

// A stated gap (docs/designissues/2026-10-28-feature-combination-safety.md, row
// `xmpp-serve --mix`): stanzas held for an offline account have no bound.
const PENDING_ISSUE = 'https://github.com/danbri/factoidal/issues/1235'
function xfail (name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false
    try { await fn() } catch (err) { failed = true; t.diagnostic(String(err && err.message)) }
    assert.ok(failed, `unexpected pass: ${name} now works; flip this xfail to an assertion and close ${issueUrl}`)
  })
}
// Fixed 2026-11-03: the engine holds, bounded (L4Factoidal/XMPP/Held.lean, hold_perAccount).
test(`past 1,000 held stanzas for an offline account, the sender gets resource-constraint (${PENDING_ISSUE})`, async () => {
  const server = await start()
  try {
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    for (let i = 0; i < 1001; i++) hag.send(`<message to='hecate@${DOMAIN}' type='chat' id='f${i}'><body>${i}</body></message>`)
    await hag.next((m) => /resource-constraint/.test(m), 3000)
    hag.ws.close()
  } finally { await server.close() }
})
