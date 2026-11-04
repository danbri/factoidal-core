// test/xmpp-state.test.mjs — xmpp-serve survives a restart, its state sealed at rest
// (issue https://github.com/danbri/factoidal/issues/1237). The state is an LWS storage in
// DIR/state that the host opens in-process as a component principal (issue 1238); what is
// written is decided by Lean (XMPP/StateCodec.lean, with round-trip theorems).

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, rmSync, readdirSync, readFileSync, statSync, writeFileSync, mkdirSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { randomBytes } from 'node:crypto'

const DOMAIN = 'example.com'
const MIX = 'mix.example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_CORE = 'urn:xmpp:mix:core:1'
const NS_PAM = 'urn:xmpp:mix:pam:2'
const NS_ROSTER = 'jabber:iq:roster'
const ACCOUNTS = [{ username: 'hag66', password: 'h3c4t3' }, { username: 'hecate', password: 'm00n' }]

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
const byId = (id) => (m) => m.includes(`id="${id}"`)
const start = (dir, stateKey) => serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
  dir, mixDomain: MIX, ...(stateKey ? { stateKey } : {}),
  websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true } })
const filesUnder = (d) => readdirSync(d, { recursive: true }).map((f) => join(d, String(f))).filter((f) => statSync(f).isFile())

test('state survives a restart: a MIX channel, a held message and a roster; nothing in clear on disk', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'xmpp-state-'))
  const key = randomBytes(32).toString('hex')
  try {
    // Run 1: a channel with two participants, a roster item, and a message held for offline hecate.
    let server = await start(dir, key)
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    hag.send(`<iq type='set' id='c1' to='${MIX}'><create xmlns='${NS_CORE}' channel='coven'/></iq>`)
    await hag.next(byId('c1'))
    for (const [who, id] of [['hag66', 'j1']]) {
      hag.send(`<iq type='set' id='${id}' to='${who}@${DOMAIN}'><client-join xmlns='${NS_PAM}' channel='coven@${MIX}'><join xmlns='${NS_CORE}'><nick>third witch</nick></join></client-join></iq>`)
      await hag.next(byId(id))
    }
    const hecate = await bound(server.wsOrigin, 'hecate', 'm00n', 'x')
    hecate.send(`<iq type='set' id='j2' to='hecate@${DOMAIN}'><client-join xmlns='${NS_PAM}' channel='coven@${MIX}'><join xmlns='${NS_CORE}'/></client-join></iq>`)
    await hecate.next(byId('j2'))
    hecate.ws.close()
    // Wait until the server has seen the close: a stanza sent to a session that is
    // closing goes to it and is lost (no XEP-0198 stream management here).
    for (let i = 0; i < 100 && server.sessions().some((x) => x.bare === `hecate@${DOMAIN}`); i++) {
      await new Promise((r) => setTimeout(r, 20))
    }
    hag.send(`<iq type='set' id='r1'><query xmlns='${NS_ROSTER}'><item jid='hecate@${DOMAIN}' name='Hecate'/></query></iq>`)
    await hag.next(byId('r1'))
    hag.send(`<message to='hecate@${DOMAIN}' type='chat' id='m1'><body>wait for me</body></message>`)
    await new Promise((r) => setTimeout(r, 300))
    hag.ws.close()
    await server.close()

    // Nothing readable on disk: no JID, no body, no nick in any file.
    const files = filesUnder(dir)
    assert.ok(files.length > 0, 'the state storage wrote files')
    for (const f of files) {
      const bytes = readFileSync(f).toString('latin1')
      for (const secret of ['wait for me', 'third witch', 'hecate@example.com', 'Hecate']) {
        assert.ok(!bytes.includes(secret), `${f} holds "${secret}" in clear`)
      }
    }

    // Run 2, same DIR and key: everything is back.
    server = await start(dir, key)
    const back = await bound(server.wsOrigin, 'hecate', 'm00n', 'y')
    assert.match(await back.next(byId('m1')), /wait for me/)
    const hag2 = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'b')
    hag2.send(`<iq type='get' id='r2'><query xmlns='${NS_ROSTER}'/></iq>`)
    assert.match(await hag2.next(byId('r2')), /name="Hecate"/)
    hag2.send(`<message to='coven@${MIX}' type='groupchat' id='g1'><body>still a coven</body></message>`)
    const m = await back.next(byId('g1'))
    assert.match(m, /<nick>third witch<\/nick>/)
    back.ws.close(); hag2.ws.close()
    await server.close()
  } finally { rmSync(dir, { recursive: true, force: true }) }
})

test('a wrong key stops the start; it does not start empty', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'xmpp-state-'))
  try {
    const server = await start(dir, randomBytes(32).toString('hex'))
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    hag.send(`<iq type='set' id='c1' to='${MIX}'><create xmlns='${NS_CORE}' channel='coven'/></iq>`)
    await hag.next(byId('c1'))
    hag.ws.close()
    await server.close()
    await assert.rejects(start(dir, randomBytes(32).toString('hex')))
  } finally { rmSync(dir, { recursive: true, force: true }) }
})

test('plaintext roster files of an earlier run are migrated into the sealed state, then deleted', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'xmpp-state-'))
  const key = randomBytes(32).toString('hex')
  try {
    mkdirSync(join(dir, 'roster'), { recursive: true })
    writeFileSync(join(dir, 'roster', 'hag66%40example.com.tsv'), `hecate@${DOMAIN}\tHecate\tnone\t0`)
    let server = await start(dir, key)
    await server.close()
    assert.deepEqual(readdirSync(join(dir, 'roster')).filter((f) => f.endsWith('.tsv')), [])
    server = await start(dir, key)
    const hag = await bound(server.wsOrigin, 'hag66', 'h3c4t3', 'a')
    hag.send(`<iq type='get' id='r3'><query xmlns='${NS_ROSTER}'/></iq>`)
    assert.match(await hag.next(byId('r3')), /name="Hecate"/)
    hag.ws.close()
    await server.close()
  } finally { rmSync(dir, { recursive: true, force: true }) }
})
