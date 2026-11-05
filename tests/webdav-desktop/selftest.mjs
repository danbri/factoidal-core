// Self-test of the desktop WebDAV lab harness, with no desktop client.
// https://github.com/danbri/factoidal/issues/1079
//
//   node tests/webdav-desktop/selftest.mjs [--cli PATH]
//
// Starts authenticated LWS, seeds every tree, and reads it through read-only
// WebDAV and the recording proxy. Checks all eight write refusals and then
// checks every seeded file byte for byte and every path for changes.
//
// It checks the harness. It is not a check of any desktop client; those are
// probe-*.sh, probe-windows.ps1 and checklist.md.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, rmSync, existsSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { run, factoidalCommand, startServer, stopServer } from './serve-labs.mjs'
import { davRequest, encodePath, parseMultistatus, walkMount } from './seed.mjs'
import { TREES, materialise } from '../../labs/filetrees/trees.mjs'

let passed = 0
let failed = 0
const failures = []
async function check (name, body) {
  try { await body(); passed += 1; console.log(`  ok    ${name}`) } catch (e) { failed += 1; failures.push(`${name}: ${e && e.message ? e.message : e}`); console.log(`  FAIL  ${name}`) }
}
function assert (cond, msg) { if (!cond) throw new Error(msg) }
const cliIndex = process.argv.indexOf('--cli')
const cli = cliIndex > 0 ? resolve(process.argv[cliIndex + 1]) : null
if (factoidalCommand(cli)[0].startsWith('npx') && !process.argv.includes('--allow-npx')) {
  console.error('webdav desktop harness: no engine in this checkout; provide --cli or FACTOIDAL_CLI (or --allow-npx for the published package)')
  console.log('webdav desktop harness: 0 pass, 1 fail, 0 skipped (out of 1)')
  process.exit(1)
}
const out = mkdtempSync(join(tmpdir(), 'factoidal-labs-selftest-'))
const started = Date.now()
let lab
try {
  lab = await run({ port: 0, trees: null, out, cli, keep: false, exitAfterSeed: false, duration: null, quiet: true })
} catch (e) {
  rmSync(out, { recursive: true, force: true })
  console.error(`webdav desktop harness: startup failed: ${e.stack || e}`)
  console.log('webdav desktop harness: 0 pass, 1 fail, 0 skipped (out of 1)')
  process.exit(1)
}
const P = lab.proxy.origin
console.log(`selftest: lab ready in ${((Date.now() - started) / 1000).toFixed(1)} s; proxy ${P}`)

try {
  // Names that every client and file system takes; a refusal of one of these is a defect.
  const portable = new Set(['types', 'links', 'config', 'hidden', 'sizes', 'many', 'deep'])
  await check('seed: every entry of the portable trees is put (201 or 204)', async () => {
    const bad = lab.seed.filter((t) => portable.has(t.tree)).flatMap((t) => t.results.filter((r) => !r.ok).map((r) => `${t.tree}/${r.path} ${r.status}`))
    assert(bad.length === 0, bad.join(', '))
  })
  await check('seed: names tree, the plain names are put', async () => {
    const names = lab.seed.find((t) => t.tree === 'names').results
    for (const n of ['with space.txt', 'café-nfc.txt', 'café-nfd.txt', 'emoji-\u{1F989}.txt', 'NAMES.txt']) {
      const r = names.find((x) => x.path === n)
      assert(r && r.ok, `${JSON.stringify(n)}: ${r ? r.status : 'absent'}`)
    }
    const refused = names.filter((r) => !r.ok)
    console.log(`        names refused by the server (a finding, not a failure): ${refused.length ? refused.map((r) => `${JSON.stringify(r.path)} ${r.status}`).join(', ') : 'none'}`)
  })
  await check('proxy: PROPFIND / lists one folder per tree', async () => {
    const r = await davRequest(P, 'PROPFIND', '/', { headers: { depth: '1' } })
    assert(r.status === 207, `status ${r.status}`)
    const hrefs = parseMultistatus(r.body.toString('utf8')).map((i) => i.href)
    for (const t of TREES) assert(hrefs.includes(`/${t.name}/`), `no /${t.name}/ in ${hrefs.join(' ')}`)
  })
  await check('proxy: many tree lists 1,000 files', async () => {
    const items = await walkMount(P, 'many')
    assert(items.length === 1000, `${items.length}`)
  })
  await check('proxy: deep tree leaf at depth 32 reads', async () => {
    const segs = []
    for (let i = 1; i <= 32; i++) segs.push(`level-${String(i).padStart(2, '0')}`)
    const r = await davRequest(P, 'GET', `/deep/${segs.join('/')}/leaf.txt`)
    assert(r.status === 200 && r.body.toString() === 'depth 32\n', `${r.status}`)
  })
  await check('proxy: link file names the proxy origin', async () => {
    const r = await davRequest(P, 'GET', '/links/open-dashboard.webloc')
    assert(r.body.toString().includes(`${P}/links/dashboard.html`), r.body.toString())
  })
  const before = new Map()
  await check('proxy: record every path before write attempts', async () => {
    for (const t of TREES) before.set(t.name, await walkMount(P, t.name))
  })
  const target = '/config/config/example-sparql/remote_sparql.txt'
  const tmp = '/config/config/example-sparql/.remote_sparql.txt.sb-1234'
  const writes = [
    ['PUT', tmp, { body: Buffer.from('changed\n') }],
    ['PUT', target, { body: Buffer.from('changed\n') }],
    ['PUT', '/types/._hello.txt', { body: Buffer.from([0, 5, 22, 7]) }],
    ['DELETE', target, {}],
    ['MKCOL', '/config/new-folder/', {}],
    ['COPY', target, { headers: { destination: `${P}${target}.copy` } }],
    ['MOVE', tmp, { headers: { destination: `${P}${target}`, overwrite: 'T' } }],
    ['PROPPATCH', target, { body: Buffer.from('<propertyupdate xmlns="DAV:"><set><prop><label xmlns="urn:test">changed</label></prop></set></propertyupdate>') }],
    ['LOCK', '/types/hello.txt', { headers: { 'content-type': 'application/xml', timeout: 'Second-60', depth: '0' }, body: Buffer.from('<lockinfo xmlns="DAV:"><lockscope><exclusive/></lockscope><locktype><write/></locktype><owner>selftest</owner></lockinfo>') }],
    ['UNLOCK', '/types/hello.txt', { headers: { 'lock-token': '<urn:uuid:00000000-0000-4000-8000-000000000000>' } }]
  ]
  for (const [method, path, opts] of writes) {
    await check(`read only: ${method} ${path} is refused`, async () => {
      const r = await davRequest(P, method, path, opts)
      assert(r.status === 403, `${r.status}: ${r.body}`)
      assert(r.headers.allow === 'OPTIONS, GET, HEAD, PROPFIND', `Allow: ${r.headers.allow}`)
      assert(r.body.toString().includes('read only (emergency mode'), `${r.body}`)
    })
  }
  await check('read only: all paths and sizes are unchanged after write attempts', async () => {
    for (const t of TREES) {
      const after = await walkMount(P, t.name)
      assert(before.has(t.name) && JSON.stringify(after) === JSON.stringify(before.get(t.name)), `${t.name}: tree changed`)
    }
  })
  await check('read only: every accepted non-sizes file still has its exact original bytes (including Unicode names)', async () => {
    for (const t of TREES.filter((t) => t.name !== 'sizes')) {
      const accepted = new Set(lab.seed.find((s) => s.tree === t.name).results.filter((r) => r.ok && r.kind === 'file').map((r) => r.path))
      for (const e of materialise(t, { origin: P })) {
        if (e.dir || !accepted.has(e.path)) continue
        const r = await davRequest(P, 'GET', `/${t.name}/${encodePath(e.path)}`)
        assert(r.status === 200 && r.body.equals(e.data), `${t.name}/${e.path}: ${r.status}, bytes differ`)
      }
    }
  })
  await check('guest labs: credentials cannot fall back to guest', async () => {
    const r = await davRequest(P, 'GET', '/types/hello.txt', { headers: { authorization: 'Basic ' + Buffer.from('labs:wrong').toString('base64') } })
    assert(r.status === 401, `${r.status}`)
  })
  await check('no guest: unauthenticated read is 401', async () => {
    const web = await startServer(lab.config, factoidalCommand(cli), [])
    try {
      const r = await davRequest(web.origin, 'GET', '/types/hello.txt')
      assert(r.status === 401 && r.headers['www-authenticate']?.startsWith('Basic '), `${r.status}`)
    } finally { await stopServer(web.child) }
  })
  await check('mount users: another guest sees no labs mounts and cannot read them', async () => {
    const web = await startServer(lab.config, factoidalCommand(cli), ['--guest', 'outsider'])
    try {
      const root = await davRequest(web.origin, 'PROPFIND', '/', { headers: { depth: '1' } })
      assert(root.status === 207 && parseMultistatus(root.body.toString()).every((i) => i.href === '/'), `${root.status}: ${root.body}`)
      const r = await davRequest(web.origin, 'GET', '/types/hello.txt')
      const missing = await davRequest(web.origin, 'GET', '/missing/hello.txt')
      assert(r.status === 404 && missing.status === 404 && r.body.equals(missing.body), `${r.status}, ${missing.status}`)
    } finally { await stopServer(web.child) }
  })
  // Keep the expensive size reads last: a large-file engine crash must not
  // prevent the write refusal and mount/user checks above from running.
  const sizeEntries = materialise(TREES.find((t) => t.name === 'sizes'), { origin: P })
  const originalSums = sizeEntries.find((e) => e.path === 'SHA256SUMS').data.toString('utf8')
  await check('proxy: sizes SHA256SUMS has its exact original bytes', async () => {
    const r = await davRequest(P, 'GET', '/sizes/SHA256SUMS')
    assert(r.status === 200 && r.body.toString('utf8') === originalSums, `${r.status}: manifest changed`)
    assert(originalSums.trim().split('\n').length === 6, 'expected six size fixtures')
  })
  for (const e of sizeEntries.filter((e) => e.path !== 'SHA256SUMS')) {
    await check(`proxy: sizes/${e.path} has its original size, bytes and SHA256SUMS hash`, async () => {
      const hex = originalSums.trim().split('\n').find((line) => line.endsWith(`  ${e.path}`))?.split(/\s+/)[0]
      assert(hex, `no original checksum for ${e.path}`)
      const r = await davRequest(P, 'GET', `/sizes/${e.path}`)
      assert(r.status === 200, `${e.path}: ${r.status}: ${r.body.toString('utf8').slice(0, 200)}`)
      assert(r.body.equals(e.data), `${e.path}: original bytes differ`)
      assert(createHash('sha256').update(r.body).digest('hex') === hex, `${e.path}: digest differs`)
    })
  }

} finally {
  await lab.stop()
}

const read = (f) => readFileSync(join(out, f), 'utf8')
await check('results: seed.json, requests.jsonl, summary.md, final-tree.md exist', async () => {
  for (const f of ['seed.json', 'requests.jsonl', 'summary.md', 'final-tree.md', 'environment.json', 'webdav.stderr', 'lws.stderr']) assert(existsSync(join(out, f)), f)
})
await check('results: request log has status, User-Agent and the PROPFIND/LOCK bodies', async () => {
  const recs = read('requests.jsonl').trim().split('\n').map((l) => JSON.parse(l))
  assert(recs.length >= 15, `${recs.length} records`)
  assert(recs.every((r) => typeof r.status === 'number'), 'a record has no status')
  const lock = recs.find((r) => r.method === 'LOCK')
  assert(lock && lock.status === 403 && /lockinfo/.test(lock.reqBody) && /read only/.test(lock.resBody || ''), 'LOCK refusal bodies')
  const mv = recs.find((r) => r.method === 'MOVE')
  assert(mv && mv.reqHeaders.destination, 'MOVE destination')
})
await check('results: summary.md lists refused AppleDouble and config save attempts', async () => {
  const s = read('summary.md')
  assert(/AppleDouble/.test(s) && /\._hello\.txt/.test(s), 'AppleDouble section')
  assert(/MOVE \/config\/config\/example-sparql\/\.remote_sparql\.txt\.sb-1234 -> \/config\/config\/example-sparql\/remote_sparql\.txt/.test(s), 'config save sequence')
})
await check('results: final-tree.md shows no added or removed paths', async () => {
  const s = read('final-tree.md')
  assert(!/^- (added|removed) /m.test(s), 'tree changed')
  assert(!/listing failed/.test(s), 'final listing failed')
  assert((s.match(/0 added; 0 removed/g) || []).length === TREES.length, 'missing tree report')
})

if (failed === 0) rmSync(out, { recursive: true, force: true })
else console.log(`selftest: results kept in ${out}`)
console.log(`webdav desktop harness: ${passed} pass, ${failed} fail, 0 xfail, 0 skipped (out of ${passed + failed})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
