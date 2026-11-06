// test/xmpp-muc-moderation.test.mjs — XEP-0045 sections 8 to 10 in the Node XMPP host, against the
// Lean engine (L4Factoidal/XMPP/Muc.lean; theorems outcast_cannot_join, roleRefusal_below_admin,
// configured_owner_fixed, setAff_keeps_owner, join_no_first_owner, ban_gone) and the kept state
// (XMPP/StateCodec.lean, decodeAcl_encodeAcl). Clients speak RFC 7395 over Node's own WebSocket.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, rmSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join as pathJoin, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { randomBytes } from 'node:crypto'
import { spawn } from 'node:child_process'

const DOMAIN = 'example.com'
const MUC = 'conference.example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_FRAMING = 'urn:ietf:params:xml:ns:xmpp-framing'
const NS_MUC = 'http://jabber.org/protocol/muc'
const NS_ADMIN = 'http://jabber.org/protocol/muc#admin'
const NS_OWNER = 'http://jabber.org/protocol/muc#owner'
const ACCOUNTS = [{ username: 'boss', password: 'b0ss' }, { username: 'juliet', password: 'r0m30' },
  { username: 'romeo', password: 'juli3t' }, { username: 'mallory', password: 'evil' }]
const PASSWORD = Object.fromEntries(ACCOUNTS.map((a) => [a.username, a.password]))

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

async function bound (url, user, resource = 'r') {
  const c = wsClient(url)
  await c.opened
  c.send(open)
  await c.next((m) => m.startsWith('<stream:features'))
  c.send(plain(user, PASSWORD[user]))
  await c.next((m) => m.startsWith('<success'))
  c.send(open)
  await c.next((m) => m.startsWith('<stream:features'))
  c.send(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>${resource}</resource></bind></iq>`)
  await c.next((m) => m.includes('<jid>'))
  return c
}

const OWNERS = [{ room: '*', owners: [`boss@${DOMAIN}`] }]
const start = (extra = {}) => serverModule.listen({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {},
  mucDomain: MUC, disableRateLimits: true, websocket: { port: 0, path: '/xmpp-websocket', allowNoOrigin: true }, ...extra })
const self = (m) => m.startsWith('<presence') && m.includes('status code="110"')
const byId = (id) => (m) => m.includes(`id="${id}"`)
/** Join and wait for the joiner's own presence. */
async function seat (c, room, nick) {
  c.send(`<presence to='${room}@${MUC}/${nick}'><x xmlns='${NS_MUC}'/></presence>`)
  return c.next(self)
}
let serial = 0
/** An IQ to the room; answers the stanza with its id. */
async function iq (c, room, type, items, ns = NS_ADMIN) {
  const id = `q${++serial}`
  c.send(`<iq type='${type}' id='${id}' to='${room}@${MUC}'><query xmlns='${ns}'>${items}</query></iq>`)
  return c.next(byId(id))
}
const isError = (m, cond) => assert.ok(m.includes('type="error"') && m.includes(`<${cond}`), m)
const isResult = (m) => assert.ok(m.includes('type="result"'), m)

test('moderation: the first occupant has no rights on a server with an owner configuration', async () => {
  const s = await start({ mucOwners: OWNERS })
  try {
    const m = await bound(s.wsOrigin, 'mallory')
    const first = await seat(m, 'tea', 'mal')
    assert.match(first, /code="201"/)
    assert.match(first, /affiliation="none"/)
    assert.match(first, /role="participant"/)
    isError(await iq(m, 'tea', 'set', `<item jid='boss@${DOMAIN}' affiliation='outcast'/>`), 'forbidden')
    isError(await iq(m, 'tea', 'get', "<item affiliation='owner'/>"), 'forbidden')
    const b = await bound(s.wsOrigin, 'boss')
    const own = await seat(b, 'tea', 'boss')
    assert.match(own, /affiliation="owner"/)
    assert.match(own, /role="moderator"/)
    m.ws.close(); b.ws.close()
  } finally { await s.close() }
})

test('moderation: kick is 307, ban is 301; a ban stops a return, and the ban list shows it', async () => {
  const s = await start({ mucOwners: OWNERS })
  try {
    const b = await bound(s.wsOrigin, 'boss')
    await seat(b, 'tea', 'boss')
    const r = await bound(s.wsOrigin, 'romeo')
    await seat(r, 'tea', 'rom')
    const j = await bound(s.wsOrigin, 'juliet')
    await seat(j, 'tea', 'jul')

    isResult(await iq(b, 'tea', 'set', "<item nick='rom' role='none'><reason>not now</reason></item>"))
    const kicked = await r.next((m) => m.includes('unavailable'))
    assert.match(kicked, /code="307"/)
    assert.match(kicked, /code="110"/)
    assert.match(kicked, /<actor nick="boss"/)
    assert.match(kicked, /<reason>not now<\/reason>/)
    const seen = await j.next((m) => m.includes('unavailable'))
    assert.match(seen, /code="307"/)
    assert.doesNotMatch(seen, /code="110"|actor|romeo@/)

    // A kick is not a ban.
    await seat(r, 'tea', 'rom')
    await j.next((m) => m.includes(`tea@${MUC}/rom`))

    isResult(await iq(b, 'tea', 'set', `<item jid='romeo@${DOMAIN}' affiliation='outcast'/>`))
    const banned = await r.next((m) => m.includes('unavailable'))
    assert.match(banned, /code="301"/)
    assert.match(banned, /affiliation="outcast"/)
    assert.match(await j.next((m) => m.includes('unavailable')), /code="301"/)

    r.send(`<presence to='tea@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    const refused = await r.next((m) => m.includes('type="error"'))
    assert.match(refused, /<forbidden/)
    assert.match(refused, /type="auth"/)

    assert.match(await iq(b, 'tea', 'get', "<item affiliation='outcast'/>"), new RegExp(`jid="romeo@${DOMAIN}"`))
    isResult(await iq(b, 'tea', 'set', `<item jid='romeo@${DOMAIN}' affiliation='none'/>`))
    await seat(r, 'tea', 'rom')
    r.ws.close(); j.ws.close(); b.ws.close()
  } finally { await s.close() }
})

test('moderation: voice, and a moderator who cannot act on an admin or an owner', async () => {
  const s = await start({ mucOwners: OWNERS })
  try {
    const b = await bound(s.wsOrigin, 'boss')
    await seat(b, 'tea', 'boss')
    const r = await bound(s.wsOrigin, 'romeo')
    await seat(r, 'tea', 'rom')
    const j = await bound(s.wsOrigin, 'juliet')
    await seat(j, 'tea', 'jul')
    const m = await bound(s.wsOrigin, 'mallory')
    await seat(m, 'tea', 'mal')

    // A participant has no powers.
    isError(await iq(m, 'tea', 'set', "<item nick='rom' role='none'/>"), 'forbidden')

    // Romeo is a moderator; Juliet an admin.
    isResult(await iq(b, 'tea', 'set', "<item nick='rom' role='moderator'/>"))
    assert.match(await r.next((x) => self(x) && x.includes('role="moderator"')), /role="moderator"/)
    isResult(await iq(b, 'tea', 'set', `<item jid='juliet@${DOMAIN}' affiliation='admin'/>`))
    await j.next((x) => self(x) && x.includes('affiliation="admin"'))

    isError(await iq(r, 'tea', 'set', "<item nick='boss' role='none'/>"), 'not-allowed')
    isError(await iq(r, 'tea', 'set', "<item nick='jul' role='none'/>"), 'not-allowed')
    isError(await iq(r, 'tea', 'set', "<item nick='jul' role='visitor'/>"), 'not-allowed')
    isError(await iq(r, 'tea', 'set', `<item jid='mallory@${DOMAIN}' affiliation='outcast'/>`), 'forbidden')
    isError(await iq(j, 'tea', 'set', "<item nick='boss' role='none'/>"), 'not-allowed')
    isError(await iq(j, 'tea', 'set', `<item jid='romeo@${DOMAIN}' affiliation='admin'/>`), 'forbidden')
    isError(await iq(j, 'tea', 'set', `<item jid='boss@${DOMAIN}' affiliation='none'/>`), 'not-allowed')
    isError(await iq(b, 'tea', 'set', `<item jid='boss@${DOMAIN}' affiliation='none'/>`), 'not-allowed')
    isError(await iq(b, 'tea', 'set', `<item jid='boss@${DOMAIN}' affiliation='outcast'/>`), 'conflict')

    // Voice: a visitor cannot send, and leaving does not bring the voice back.
    isResult(await iq(r, 'tea', 'set', "<item nick='mal' role='visitor'/>"))
    await m.next((x) => self(x) && x.includes('role="visitor"'))
    m.send(`<message to='tea@${MUC}' type='groupchat' id='g1'><body>loud</body></message>`)
    assert.match(await m.next(byId('g1')), /<forbidden/)
    m.send(`<presence to='tea@${MUC}/mal' type='unavailable'/>`)
    await m.next(self)
    assert.match(await seat(m, 'tea', 'mal'), /role="visitor"/)
    assert.match(await iq(r, 'tea', 'get', "<item role='visitor'/>"), /nick="mal"/)
    isResult(await iq(r, 'tea', 'set', "<item nick='mal' role='participant'/>"))
    await m.next((x) => self(x) && x.includes('role="participant"'))
    m.send(`<message to='tea@${MUC}' type='groupchat' id='g2'><body>calm</body></message>`)
    assert.match(await m.next(byId('g2')), /calm/)

    // Revoke moderator; the lists.
    isResult(await iq(j, 'tea', 'set', "<item nick='rom' role='participant'/>"))
    await r.next((x) => self(x) && x.includes('role="participant"'))
    assert.match(await iq(b, 'tea', 'get', "<item affiliation='admin'/>"), new RegExp(`jid="juliet@${DOMAIN}"`))
    assert.match(await iq(b, 'tea', 'get', "<item affiliation='owner'/>", NS_OWNER), new RegExp(`jid="boss@${DOMAIN}"`))
    isError(await iq(j, 'tea', 'get', "<item affiliation='owner'/>"), 'forbidden')
    assert.match(await iq(j, 'tea', 'get', "<item role='moderator'/>"), /nick="boss"/)
    for (const c of [b, r, j, m]) c.ws.close()
  } finally { await s.close() }
})

test('moderation: no owner configuration: the first occupant is the owner, and bans go with the room', async () => {
  const s = await start()
  try {
    const j = await bound(s.wsOrigin, 'juliet')
    assert.match(await seat(j, 'tea', 'jul'), /affiliation="owner"/)
    const r = await bound(s.wsOrigin, 'romeo')
    await seat(r, 'tea', 'rom')
    isResult(await iq(j, 'tea', 'set', "<item nick='rom' affiliation='outcast'/>"))
    assert.match(await r.next((m) => m.includes('unavailable')), /code="301"/)
    r.send(`<presence to='tea@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await r.next((m) => m.includes('type="error"')), /<forbidden/)
    // The last owner stays.
    isError(await iq(j, 'tea', 'set', `<item jid='juliet@${DOMAIN}' affiliation='none'/>`), 'conflict')
    j.send(`<presence to='tea@${MUC}/jul' type='unavailable'/>`)
    await j.next(self)
    assert.match(await seat(r, 'tea', 'rom'), /affiliation="owner"/)
    j.ws.close(); r.ws.close()
  } finally { await s.close() }
})

test('moderation: a members-only room: an admin adds a member; a revoked member goes with 321', async () => {
  const s = await start({ mucOwners: OWNERS, mucMembers: [{ room: 'bus', members: [`juliet@${DOMAIN}`] }] })
  try {
    const b = await bound(s.wsOrigin, 'boss')
    await seat(b, 'bus', 'boss')
    const r = await bound(s.wsOrigin, 'romeo')
    r.send(`<presence to='bus@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await r.next((m) => m.includes('type="error"')), /registration-required/)
    isResult(await iq(b, 'bus', 'set', `<item jid='romeo@${DOMAIN}' affiliation='member'/>`))
    assert.match(await seat(r, 'bus', 'rom'), /affiliation="member"/)
    isResult(await iq(b, 'bus', 'set', `<item jid='romeo@${DOMAIN}' affiliation='none'/>`))
    assert.match(await r.next((m) => m.includes('unavailable')), /code="321"/)
    isError(await iq(b, 'bus', 'set', `<item jid='juliet@${DOMAIN}' affiliation='none'/>`), 'not-allowed')
    assert.match(await iq(b, 'bus', 'get', "<item affiliation='member'/>"), new RegExp(`jid="juliet@${DOMAIN}"`))
    b.ws.close(); r.ws.close()
  } finally { await s.close() }
})

test('moderation: bans, grants and revoked voices survive a restart, sealed; a configured owner comes from the configuration', async () => {
  const dir = mkdtempSync(pathJoin(tmpdir(), 'xmpp-muc-'))
  const stateKey = randomBytes(32).toString('hex')
  try {
    let s = await start({ dir, stateKey, mucOwners: OWNERS })
    const b = await bound(s.wsOrigin, 'boss')
    await seat(b, 'tea', 'boss')
    const m = await bound(s.wsOrigin, 'mallory')
    await seat(m, 'tea', 'mal')
    isResult(await iq(b, 'tea', 'set', `<item jid='romeo@${DOMAIN}' affiliation='outcast'/>`))
    isResult(await iq(b, 'tea', 'set', `<item jid='juliet@${DOMAIN}' affiliation='admin'/>`))
    isResult(await iq(b, 'tea', 'set', "<item nick='mal' role='visitor'/>"))
    await new Promise((r) => setTimeout(r, 300))
    b.ws.close(); m.ws.close()
    await s.close()

    const files = readdirSync(dir, { recursive: true }).map((f) => pathJoin(dir, String(f))).filter((f) => statSync(f).isFile())
    assert.ok(files.length > 0)
    for (const f of files) {
      const bytes = readFileSync(f).toString('latin1')
      assert.ok(!bytes.includes(`romeo@${DOMAIN}`) && !bytes.includes('outcast'), `${f} holds a ban in clear`)
    }

    s = await start({ dir, stateKey, mucOwners: OWNERS })
    const r = await bound(s.wsOrigin, 'romeo')
    r.send(`<presence to='tea@${MUC}/rom'><x xmlns='${NS_MUC}'/></presence>`)
    assert.match(await r.next((x) => x.includes('type="error"')), /<forbidden/)
    const j = await bound(s.wsOrigin, 'juliet')
    assert.match(await seat(j, 'tea', 'jul'), /affiliation="admin"/)
    const m2 = await bound(s.wsOrigin, 'mallory')
    assert.match(await seat(m2, 'tea', 'mal'), /role="visitor"/)

    // An unban is kept too.
    const b2 = await bound(s.wsOrigin, 'boss')
    isResult(await iq(b2, 'tea', 'set', `<item jid='romeo@${DOMAIN}' affiliation='none'/>`))
    isResult(await iq(b2, 'tea', 'set', `<item jid='juliet@${DOMAIN}' affiliation='none'/>`))
    isResult(await iq(b2, 'tea', 'set', "<item nick='mal' role='participant'/>"))
    await new Promise((res) => setTimeout(res, 300))
    for (const c of [r, j, m2, b2]) c.ws.close()
    await s.close()

    // The owners are the configuration's: another list at the next start replaces them.
    s = await start({ dir, stateKey, mucOwners: [{ room: 'tea', owners: [`juliet@${DOMAIN}`] }] })
    const j2 = await bound(s.wsOrigin, 'juliet')
    assert.match(await seat(j2, 'tea', 'jul'), /affiliation="owner"/)
    const b3 = await bound(s.wsOrigin, 'boss')
    assert.match(await seat(b3, 'tea', 'boss'), /affiliation="none"/)
    const r3 = await bound(s.wsOrigin, 'romeo')
    assert.match(await seat(r3, 'tea', 'rom'), /affiliation="none"/)
    for (const c of [j2, b3, r3]) c.ws.close()
    await s.close()
  } finally { rmSync(dir, { recursive: true, force: true }) }
})

test('moderation: xmpp-serve --muc-owners: "*" is every room; a bad line stops the start', async () => {
  const dir = mkdtempSync(pathJoin(tmpdir(), 'xmpp-owners-'))
  const cli = pathJoin(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')
  const run = (args) => new Promise((resolve) => {
    const p = spawn(process.execPath, [cli, 'xmpp-serve', ...args], { stdio: ['ignore', 'pipe', 'pipe'] })
    let out = ''
    const stop = setTimeout(() => p.kill('SIGKILL'), 20000)
    p.stdout.on('data', (d) => { out += d })
    p.stderr.on('data', (d) => { out += d })
    p.on('exit', (code) => { clearTimeout(stop); resolve({ code, out, p }) })
  })
  try {
    const bad = pathJoin(dir, 'bad')
    writeFileSync(bad, 'tea: not-a-jid\n')
    const refused = await run([dir, '--domain', DOMAIN, '--muc', MUC, '--muc-owners', bad, '--port', '0'])
    assert.notEqual(refused.code, 0)
    assert.match(refused.out, /--muc-owners: not "room: bare@jid/)
    const alone = await run([dir, '--domain', DOMAIN, '--muc-owners', bad, '--port', '0'])
    assert.match(alone.out, /--muc-owners needs --muc/)
  } finally { rmSync(dir, { recursive: true, force: true }) }
})
