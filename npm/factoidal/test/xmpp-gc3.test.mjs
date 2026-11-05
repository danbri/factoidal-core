// test/xmpp-gc3.test.mjs — the GC3 ("Groupchat 3.0") PROTOTYPE in the Node XMPP host, against
// the Lean engine (L4Factoidal/XMPP/Gc3.lean: apply_no_ghost, apply_rename_ids,
// apply_remove_owner, apply_join_nicks_nodup, message_recipients, message_nonmember).
//
// There is no published GC3 specification. The behaviour checked first is what the source
// slides fix (persistent joins, stable participant JIDs, optional presence). The xfails at the
// end are one per INVENTED wire choice (https://github.com/danbri/factoidal/issues/1236): each
// fails while the prototype form is in use, and must be flipped when the code adopts a
// published form.

import { test } from 'node:test'
import assert from 'node:assert/strict'

const DOMAIN = 'example.com'
const GC3 = 'gc3.example.com'
const NS = 'urn:xmpp:gc3:prototype:0'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }, { username: 'romeo', password: 'juli3t' },
  { username: 'mallory', password: 'evil' }]
const ISSUE = 'https://github.com/danbri/factoidal/issues/1236'

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
  gc3Domain: GC3, websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
const byId = (id) => (m) => m.includes(`id="${id}"`)
const join = (c, id, nick, presence) =>
  c.send(`<iq type='set' id='${id}' to='tea@${GC3}'><join xmlns='${NS}' nick='${nick}' presence='${presence}'/></iq>`)

/** juliet (owner, events on) and romeo (member, events off) in group tea. */
async function setup (server) {
  const juliet = await bound(server.wsOrigin, 'juliet', 'r0m30', 'a')
  join(juliet, 'j1', 'jul', true)
  assert.match(await juliet.next(byId('j1')), /affiliation="owner"/)
  const romeo = await bound(server.wsOrigin, 'romeo', 'juli3t', 'x')
  join(romeo, 'j2', 'rom', false)
  const joined = await romeo.next(byId('j2'))
  assert.match(joined, /id="p2"/)
  await juliet.next((m) => /type="joined"/.test(m))
  return { juliet, romeo }
}

test('gc3: membership is persistent: an offline member still receives group messages', async () => {
  const server = await start()
  try {
    const { juliet, romeo } = await setup(server)
    romeo.ws.close()
    await new Promise((r) => setTimeout(r, 300))
    juliet.send(`<message to='tea@${GC3}' type='groupchat' id='m1'><body>still there?</body></message>`)
    const own = await juliet.next(byId('m1'))
    assert.match(own, new RegExp(`from="tea@${GC3}/p1"`))
    assert.match(own, /<occupant-id xmlns="urn:xmpp:occupant-id:0" id="p1"\/>/)
    const back = await bound(server.wsOrigin, 'romeo', 'juli3t', 'y')
    assert.match(await back.next(byId('m1')), /still there\?/)
    juliet.ws.close(); back.ws.close()
  } finally { await server.close() }
})

test('gc3: a rename keeps the participant JID; only events subscribers hear it', async () => {
  const server = await start()
  try {
    const { juliet, romeo } = await setup(server)
    romeo.send(`<iq type='set' id='n1' to='tea@${GC3}'><nick xmlns='${NS}'>romeo</nick></iq>`)
    await romeo.next(byId('n1'))
    assert.match(await juliet.next((m) => /type="renamed"/.test(m)), /id="p2" nick="romeo"/)
    romeo.send(`<message to='tea@${GC3}' type='groupchat' id='m2'><body>same me</body></message>`)
    assert.match(await juliet.next(byId('m2')), new RegExp(`from="tea@${GC3}/p2"`))
    await new Promise((r) => setTimeout(r, 300))
    assert.ok(!romeo.got.some((m) => /<event/.test(m)), 'a member without presence received events')
    juliet.ws.close(); romeo.ws.close()
  } finally { await server.close() }
})

test('gc3: no one adds or removes another, except an owner removing; outsiders get nothing', async () => {
  const server = await start()
  try {
    const { juliet, romeo } = await setup(server)
    const mallory = await bound(server.wsOrigin, 'mallory', 'evil', 'z')
    mallory.send(`<message to='tea@${GC3}' type='groupchat' id='s1'><body>spam</body></message>`)
    assert.match(await mallory.next(byId('s1')), /not-acceptable/)
    mallory.send(`<iq type='get' id='l1' to='tea@${GC3}'><members xmlns='${NS}'/></iq>`)
    assert.match(await mallory.next(byId('l1')), /forbidden/)
    romeo.send(`<iq type='set' id='r1' to='tea@${GC3}'><remove xmlns='${NS}' id='p1'/></iq>`)
    assert.match(await romeo.next(byId('r1')), /forbidden/)
    juliet.send(`<iq type='set' id='r2' to='tea@${GC3}'><remove xmlns='${NS}' id='p2'/></iq>`)
    assert.match(await juliet.next(byId('r2')), /type="result"/)
    assert.match(await romeo.next((m) => /type="removed"/.test(m)), /id="p2"/)
    juliet.send(`<iq type='get' id='l2' to='tea@${GC3}'><members xmlns='${NS}'/></iq>`)
    const list = await juliet.next(byId('l2'))
    // p2 is gone; the list names no member's real JID (the result's own `to` is juliet's).
    assert.ok(!list.includes('id="p2"') && !list.includes('romeo@'), list)
    assert.match(list, /id="p1" nick="jul" affiliation="owner"/)
    juliet.ws.close(); romeo.ws.close(); mallory.ws.close()
  } finally { await server.close() }
})

// ── one xfail per invented wire choice (issue 1236) ──────────────────────
function xfail (name, fn) {
  test(`xfail: GC3 ${name} (${ISSUE})`, async (t) => {
    let failed = false
    try { await fn() } catch (err) { failed = true; t.diagnostic(String(err && err.message)) }
    assert.ok(failed, `unexpected pass: ${name}; flip this xfail to an assertion and tick it in ${ISSUE}`)
  })
}
async function discoFeatures () {
  const server = await start()
  try {
    const c = await bound(server.wsOrigin, 'juliet', 'r0m30', 'a')
    c.send(`<iq type='get' id='d1' to='${GC3}'><query xmlns='http://jabber.org/protocol/disco#info'/></iq>`)
    const r = await c.next(byId('d1'))
    c.ws.close()
    return r
  } finally { await server.close() }
}
xfail('uses a published namespace, not urn:xmpp:gc3:prototype:0', async () => {
  assert.ok(!(await discoFeatures()).includes('urn:xmpp:gc3:prototype:0'))
})
xfail('is a mode of the MUC service, not a service of its own', async () => {
  assert.fail('GC3 runs as its own service (--gc3); the slides suggest MUC with incremental changes')
})
xfail('joins with a published payload, not <join nick presence/> to the group', async () => {
  assert.fail('the <join/> IQ payload is invented')
})
xfail('leaves, renames, removes and lists with published payloads', async () => {
  assert.fail('<leave/>, <nick/>, <remove/> and <members/> are invented')
})
xfail('participant ids are opaque (XEP-0421 section 4), not p1, p2, … in join order', async () => {
  const server = await start()
  try {
    const c = await bound(server.wsOrigin, 'juliet', 'r0m30', 'a')
    join(c, 'j1', 'jul', false)
    const r = await c.next(byId('j1'))
    c.ws.close()
    assert.ok(!/id="p1"/.test(r), r)
  } finally { await server.close() }
})
xfail('membership events use a published form, not <event type/>', async () => {
  assert.fail('the <event/> notice is invented')
})
xfail('group messages follow a published delivery rule (to the bare JID, from group/<id>)', async () => {
  assert.fail('delivery to every member\'s bare JID, from group/<id>, is this prototype\'s choice')
})
