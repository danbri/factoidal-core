// test/xmpp-muc.test.mjs — XEP-0045 multi-user chat in the Node XMPP host, against the Lean
// engine (L4Factoidal/XMPP/Muc.lean, theorems groupchat_recipients, groupchat_from_sender,
// groupchat_nonoccupant, joinRoom_nodup, leaveRoom_gone). Clients speak RFC 7395 over Node's
// own WebSocket; the rooms are shared by every session of one server.

import { test } from 'node:test'
import assert from 'node:assert/strict'

const DOMAIN = 'example.com'
const MUC = 'conference.example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_MUC = 'http://jabber.org/protocol/muc'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }, { username: 'romeo', password: 'juli3t' },
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

const start = (muc = MUC) => serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
  ...(muc ? { mucDomain: muc } : {}),
  websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
const join = (c, room, nick) => c.send(`<presence to='${room}@${MUC}/${nick}'><x xmlns='${NS_MUC}'/></presence>`)
const settle = () => new Promise((r) => setTimeout(r, 300))

test('muc: disco finds the service; join, groupchat, private message, leave', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    juliet.send(`<iq type='get' id='d1' to='${DOMAIN}'><query xmlns='http://jabber.org/protocol/disco#items'/></iq>`)
    assert.match(await juliet.next((m) => /id="d1"/.test(m)), new RegExp(`jid="${MUC}"`))

    join(juliet, 'tea', 'jul')
    const self = await juliet.next((m) => m.startsWith('<presence') && /code="110"/.test(m))
    assert.match(self, /code="201"/)
    assert.match(self, /affiliation="owner"/)
    await juliet.next((m) => /<subject/.test(m))

    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    join(romeo, 'tea', 'rom')
    const seesJul = await romeo.next((m) => m.startsWith('<presence') && m.includes(`from="tea@${MUC}/jul"`))
    assert.ok(!seesJul.includes('juliet@'), `romeo learnt juliet's real JID: ${seesJul}`)
    await romeo.next((m) => /code="110"/.test(m))
    const julSeesRom = await juliet.next((m) => m.startsWith('<presence') && m.includes(`from="tea@${MUC}/rom"`))
    assert.ok(!julSeesRom.includes('romeo@'), julSeesRom)

    // A groupchat message reaches both occupants, stamped with the sender's nick.
    romeo.send(`<message to='tea@${MUC}' type='groupchat' id='g1'><body>wherefore</body></message>`)
    for (const c of [juliet, romeo]) {
      const m = await c.next((x) => /id="g1"/.test(x))
      assert.match(m, new RegExp(`from="tea@${MUC}/rom"`))
      assert.match(m, /<body>wherefore<\/body>/)
    }

    // A private message goes to the one occupant only.
    juliet.send(`<message to='tea@${MUC}/rom' type='chat' id='p1'><body>psst</body></message>`)
    assert.match(await romeo.next((x) => /id="p1"/.test(x)), new RegExp(`from="tea@${MUC}/jul"`))

    // Leaving: the other occupant hears it.
    romeo.send(`<presence to='tea@${MUC}/rom' type='unavailable'/>`)
    assert.match(await juliet.next((m) => m.includes(`from="tea@${MUC}/rom"`) && /unavailable/.test(m)), /role="none"/)
    juliet.ws.close(); romeo.ws.close()
  } finally { await server.close() }
})

test('muc: a nick conflict is refused, and an outsider cannot post', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    join(juliet, 'tea', 'jul')
    await juliet.next((m) => /code="110"/.test(m))
    const mallory = await bound(server.wsOrigin, 'mallory', 'evil', 'x')
    join(mallory, 'tea', 'jul')
    assert.match(await mallory.next((m) => m.startsWith('<presence') && /type="error"/.test(m)), /conflict/)
    mallory.send(`<message to='tea@${MUC}' type='groupchat' id='spam'><body>buy now</body></message>`)
    assert.match(await mallory.next((m) => /id="spam"/.test(m)), /not-acceptable/)
    await settle()
    assert.ok(!juliet.got.some((m) => /buy now/.test(m)), 'an outsider reached the room')
    juliet.ws.close(); mallory.ws.close()
  } finally { await server.close() }
})

test('muc: a session that disconnects leaves its rooms', async () => {
  const server = await start()
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    join(juliet, 'tea', 'jul')
    await juliet.next((m) => /code="110"/.test(m))
    const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'orchard')
    join(romeo, 'tea', 'rom')
    await juliet.next((m) => m.includes(`from="tea@${MUC}/rom"`))
    romeo.ws.close()
    assert.match(await juliet.next((m) => m.includes(`from="tea@${MUC}/rom"`) && /unavailable/.test(m)), /unavailable/)
    // Romeo's old occupant record is gone: a new session can take the nick.
    const romeo2 = await bound(server.wsOrigin, 'romeo', 'juli3t', 'garden')
    join(romeo2, 'tea', 'rom')
    await romeo2.next((m) => /code="110"/.test(m))
    juliet.ws.close(); romeo2.ws.close()
  } finally { await server.close() }
})

test('muc: off unless configured', async () => {
  const server = await start(null)
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    juliet.send(`<iq type='get' id='d2' to='${DOMAIN}'><query xmlns='http://jabber.org/protocol/disco#items'/></iq>`)
    const items = await juliet.next((m) => /id="d2"/.test(m))
    assert.ok(!items.includes(MUC), items)
    juliet.ws.close()
  } finally { await server.close() }
})
