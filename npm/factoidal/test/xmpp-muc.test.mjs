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

test('muc: a members-only room refuses anyone else and stays hidden from them', async (t) => {
  let server
  try {
    server = await serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, mucDomain: MUC,
      mucMembers: [{ room: 'bus', members: [`juliet@${DOMAIN}`, `romeo@${DOMAIN}`] }],
      websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
  } catch (error) {
    if (/does not carry members-only/.test(error.message)) return t.skip('an older engine: the host refused to start, as it should')
    throw error
  }
  try {
    const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'balcony')
    join(juliet, 'bus', 'jul')
    await juliet.next((m) => /code="110"/.test(m))
    const mallory = await bound(server.wsOrigin, 'mallory', 'evil', 'x')
    join(mallory, 'bus', 'mal')
    const refused = await mallory.next((m) => m.startsWith('<presence') && /type="error"/.test(m))
    assert.match(refused, /type="auth"/)
    assert.match(refused, /registration-required/)
    mallory.send(`<message to='bus@${MUC}' type='groupchat' id='spam'><body>buy now</body></message>`)
    assert.match(await mallory.next((m) => /id="spam"/.test(m)), /not-acceptable/)
    mallory.send(`<iq type='get' id='i1' to='${MUC}'><query xmlns='http://jabber.org/protocol/disco#items'/></iq>`)
    assert.ok(!(await mallory.next((m) => /id="i1"/.test(m))).includes('bus@'), 'the room is listed to a non-member')
    juliet.send(`<iq type='get' id='i2' to='bus@${MUC}'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>`)
    assert.match(await juliet.next((m) => /id="i2"/.test(m)), /muc_membersonly/)
    await settle()
    assert.ok(!juliet.got.some((m) => /buy now|mal/.test(m)), 'a non-member reached the room')
    // A room with no list stays open.
    join(mallory, 'tea', 'mal')
    await mallory.next((m) => /code="110"/.test(m))
    juliet.ws.close(); mallory.ws.close()
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

test('muc: a session that ends its stream cleanly leaves its rooms, and frees its nick', async () => {
  const s = await start()
  try {
    const a = await bound(s.wsOrigin, 'juliet', 'r0m30', 'one')
    a.send(`<presence to='clean@${MUC}/jul'><x xmlns='${NS_MUC}'/></presence>`)
    await a.next((m) => m.includes(`status code='110'`) || m.includes('status code="110"'))
    const b = await bound(s.wsOrigin, 'romeo', 'juli3t', 'one')
    b.send(`<presence to='clean@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    await b.next((m) => m.includes(`status code='110'`) || m.includes('status code="110"'))
    a.send(`<close xmlns='${NS_FRAMING}'/>`)
    await b.next((m) => m.includes(`clean@${MUC}/jul`) && m.includes('unavailable'))
    const c = await bound(s.wsOrigin, 'juliet', 'r0m30', 'two')
    c.send(`<presence to='clean@${MUC}/jul'><x xmlns='${NS_MUC}'/></presence>`)
    const joined = await c.next((m) => m.includes(`status code='110'`) || m.includes('status code="110"') || m.includes('conflict'))
    assert.doesNotMatch(joined, /conflict/)
    b.ws.close(); c.ws.close()
  } finally { await s.close() }
})

test('muc: an account name is reserved for that account; a nick differing only in case is taken; a nick with a space at the end is refused', async () => {
  const s = await start()
  try {
    const r = await bound(s.wsOrigin, 'romeo', 'juli3t', 'one')
    r.send(`<presence to='nicks@${MUC}/juliet'><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await r.next((m) => m.includes('type="error"')), /conflict/)
    r.send(`<presence to='nicks@${MUC}/rom '><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await r.next((m) => m.includes('not-acceptable') || m.includes('status code')), /not-acceptable/)
    r.send(`<presence to='nicks@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    await r.next((m) => m.includes(`status code='110'`) || m.includes('status code="110"'))
    const j = await bound(s.wsOrigin, 'juliet', 'r0m30', 'one')
    j.send(`<presence to='nicks@${MUC}/ROM'><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await j.next((m) => m.includes('type="error"')), /conflict/)
    j.send(`<presence to='nicks@${MUC}/juliet'><x xmlns='${NS_MUC}'/></presence>`)
    await j.next((m) => m.includes(`status code='110'`) || m.includes('status code="110"'))
    r.ws.close(); j.ws.close()
  } finally { await s.close() }
})

test('muc: XEP-0421: one occupant id for an account in a room, also under a new nick; none for another account', async () => {
  const s = await start()
  const idOf = (m) => /<occupant-id[^>]*\bid="([^"]+)"/.exec(m)?.[1]
  const self = (m) => m.includes(`status code='110'`) || m.includes('status code="110"')
  try {
    const a = await bound(s.wsOrigin, 'juliet', 'r0m30', 'one')
    a.send(`<presence to='ids@${MUC}/first'><x xmlns='${NS_MUC}'/></presence>`)
    const id1 = idOf(await a.next(self))
    assert.ok(id1)
    assert.ok(!id1.includes('juliet'))
    const r = await bound(s.wsOrigin, 'romeo', 'juli3t', 'one')
    r.send(`<presence to='ids@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    const idR = idOf(await r.next(self))
    assert.notEqual(idR, id1)
    a.send(`<presence to='ids@${MUC}/first' type='unavailable'/>`)
    await r.next((m) => m.includes('unavailable'))
    a.send(`<presence to='ids@${MUC}/second'><x xmlns='${NS_MUC}'/></presence>`)
    assert.equal(idOf(await a.next(self)), id1)
    a.send(`<message to='ids@${MUC}' type='groupchat' id='g'><body>hi</body><occupant-id xmlns='urn:xmpp:occupant-id:0' id='forged'/></message>`)
    const m = await r.next((x) => x.includes('<body>hi</body>'))
    assert.equal(idOf(m), id1)
    assert.doesNotMatch(m, /forged/)
    a.ws.close(); r.ws.close()
  } finally { await s.close() }
})

test('muc: two clients that ask for one resource each hold a seat of their own', async () => {
  const s = await start()
  const self = (m) => m.includes(`status code='110'`) || m.includes('status code="110"')
  try {
    const one = await bound(s.wsOrigin, 'juliet', 'r0m30', 'same')
    const two = await bound(s.wsOrigin, 'juliet', 'r0m30', 'same')
    one.send(`<presence to='seat@${MUC}/jul'><x xmlns='${NS_MUC}'/></presence>`)
    await one.next(self)
    two.send(`<presence to='seat@${MUC}/jul2'><x xmlns='${NS_MUC}'/></presence>`)
    await two.next(self)
    const r = await bound(s.wsOrigin, 'romeo', 'juli3t', 'one')
    r.send(`<presence to='seat@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    await r.next(self)
    r.send(`<message to='seat@${MUC}' type='groupchat' id='g0'><body>to both</body></message>`)
    await one.next((m) => m.includes('to both'))
    await two.next((m) => m.includes('to both'))
    one.send(`<close xmlns='${NS_FRAMING}'/>`)
    one.ws.close()
    await r.next((m) => m.includes(`seat@${MUC}/jul`) && m.includes('unavailable'))
    r.send(`<message to='seat@${MUC}' type='groupchat' id='g1'><body>still there</body></message>`)
    await two.next((m) => m.includes('still there'))
    two.ws.close()
    await r.next((m) => m.includes(`seat@${MUC}/jul2`) && m.includes('unavailable'))
    r.ws.close()
  } finally { await s.close() }
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
