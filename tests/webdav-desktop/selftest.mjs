// Self-test of the desktop WebDAV lab harness, with no desktop client.
// https://github.com/danbri/factoidal/issues/1079
//
//   node tests/webdav-desktop/selftest.mjs [--cli PATH]
//
// Starts serve-labs (every tree), then acts as a client through the recording
// proxy: lists the mounts, checks SHA256SUMS of the sizes tree, reads a link
// file, saves a config file the way an atomic-save editor does (PUT a
// temporary file, MOVE it over the old one), takes and releases a lock, and
// writes an AppleDouble file. Then it stops the lab and checks that seed.json,
// requests.jsonl, summary.md and final-tree.md say what happened.
//
// It checks the harness. It is not a check of any desktop client; those are
// probe-*.sh, probe-windows.ps1 and checklist.md.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, rmSync, existsSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { run, factoidalCommand } from './serve-labs.mjs'
import { davRequest, encodePath, parseMultistatus, walkMount } from './seed.mjs'
import { TREES } from '../../labs/filetrees/trees.mjs'

let passed = 0
let failed = 0
const failures = []
async function check (name, body) {
  try { await body(); passed += 1; console.log(`  ok    ${name}`) } catch (e) { failed += 1; failures.push(`${name}: ${e && e.message ? e.message : e}`); console.log(`  FAIL  ${name}`) }
}
function assert (cond, msg) { if (!cond) throw new Error(msg) }
// An expected failure tied to an open issue: it counts as xfail while it
// fails, and as a failure (stale xfail) once it passes, so the issue is closed
// and the check made a plain one (CLAUDE.md, "A stated shortfall is a failing
// test plus an open issue").
let xfailed = 0
async function xfail (name, issue, body) {
  try { await body() } catch (e) { xfailed += 1; console.log(`  xfail ${name} - ${issue}: ${e && e.message ? e.message : e}`); return }
  failed += 1
  failures.push(`${name}: passes now; close ${issue} and make this a plain check`)
  console.log(`  FAIL  ${name} (stale xfail, ${issue})`)
}

const cliIndex = process.argv.indexOf('--cli')
const cli = cliIndex > 0 ? resolve(process.argv[cliIndex + 1]) : null
if (factoidalCommand(cli)[0].startsWith('npx') && !process.argv.includes('--allow-npx')) {
  console.log('  skip  every check - no engine in this checkout (tools/fetch-builds.sh), no --cli and no FACTOIDAL_CLI; --allow-npx uses the published package')
  console.log('webdav desktop harness: 0 pass, 0 fail, 0 xfail, 1 skipped (out of 1)')
  process.exit(0)
}
const out = mkdtempSync(join(tmpdir(), 'factoidal-labs-selftest-'))
const started = Date.now()
const lab = await run({ port: 0, trees: null, out, cli, keep: false, exitAfterSeed: false, duration: null, quiet: true })
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
  await check('proxy: sizes tree matches SHA256SUMS byte for byte', async () => {
    const sums = (await davRequest(P, 'GET', '/sizes/SHA256SUMS')).body.toString('utf8').trim().split('\n')
    assert(sums.length === 6, `${sums.length} lines`)
    for (const line of sums) {
      const [hex, name] = line.split(/\s+/)
      const r = await davRequest(P, 'GET', `/sizes/${name}`)
      assert(r.status === 200, `${name} ${r.status}`)
      assert(createHash('sha256').update(r.body).digest('hex') === hex, `${name} digest`)
    }
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
  await check('proxy: atomic save (PUT temp, MOVE over the old file) through the proxy', async () => {
    const target = '/config/config/example-sparql/remote_sparql.txt'
    const tmp = '/config/config/example-sparql/.remote_sparql.txt.sb-1234'
    const put = await davRequest(P, 'PUT', tmp, { headers: { 'content-type': 'text/plain' }, body: Buffer.from('https://dbpedia.org/sparql\n') })
    assert(put.status === 201 || put.status === 204, `PUT ${put.status}`)
    const mv = await davRequest(P, 'MOVE', tmp, { headers: { destination: `${P}${target}`, overwrite: 'T' } })
    assert(mv.status === 201 || mv.status === 204, `MOVE ${mv.status}: ${mv.body}`)
    const get = await davRequest(P, 'GET', target)
    assert(get.body.toString() === 'https://dbpedia.org/sparql\n', get.body.toString())
  })
  await check('proxy: LOCK and UNLOCK a file', async () => {
    const body = Buffer.from('<?xml version="1.0"?><lockinfo xmlns="DAV:"><lockscope><exclusive/></lockscope><locktype><write/></locktype><owner>selftest</owner></lockinfo>')
    const lock = await davRequest(P, 'LOCK', '/types/hello.txt', { headers: { 'content-type': 'application/xml', timeout: 'Second-60', depth: '0' }, body })
    assert(lock.status === 200, `LOCK ${lock.status}`)
    const token = lock.headers['lock-token']
    assert(token, 'no Lock-Token')
    const un = await davRequest(P, 'UNLOCK', '/types/hello.txt', { headers: { 'lock-token': token } })
    assert(un.status === 204, `UNLOCK ${un.status}`)
  })
  await check('proxy: a client-made AppleDouble file is accepted', async () => {
    const r = await davRequest(P, 'PUT', `/types/${encodePath('._hello.txt')}`, { body: Buffer.from([0, 5, 22, 7, 0, 2, 0, 0]) })
    assert(r.status === 201 || r.status === 204, `${r.status}`)
  })
  await xfail('PUT with no Content-Type of a .txt name is stored as text/plain', 'https://github.com/danbri/factoidal/issues/1122', async () => {
    const put = await davRequest(P, 'PUT', '/config/no-content-type.txt', { body: Buffer.from('plain\n') })
    assert(put.status === 201 || put.status === 204, `PUT ${put.status}`)
    const r = await davRequest(P, 'PROPFIND', '/config/no-content-type.txt', { headers: { depth: '0' } })
    await davRequest(P, 'DELETE', '/config/no-content-type.txt')
    const m = /getcontenttype>([^<]*)</.exec(r.body.toString('utf8'))
    assert(m && m[1].startsWith('text/plain'), `getcontenttype ${m ? m[1] : '(none)'}`)
  })
} finally {
  await lab.stop()
}

const read = (f) => readFileSync(join(out, f), 'utf8')
await check('results: seed.json, requests.jsonl, summary.md, final-tree.md exist', async () => {
  for (const f of ['seed.json', 'requests.jsonl', 'summary.md', 'final-tree.md', 'environment.json']) assert(existsSync(join(out, f)), f)
})
await check('results: request log has status, User-Agent and the PROPFIND/LOCK bodies', async () => {
  const recs = read('requests.jsonl').trim().split('\n').map((l) => JSON.parse(l))
  assert(recs.length >= 15, `${recs.length} records`)
  assert(recs.every((r) => typeof r.status === 'number'), 'a record has no status')
  const lock = recs.find((r) => r.method === 'LOCK')
  assert(lock && /lockinfo/.test(lock.reqBody) && /lockdiscovery|activelock/.test(lock.resBody || ''), 'LOCK bodies')
  const mv = recs.find((r) => r.method === 'MOVE')
  assert(mv && mv.reqHeaders.destination, 'MOVE destination')
})
await check('results: summary.md lists the AppleDouble write and the config save', async () => {
  const s = read('summary.md')
  assert(/AppleDouble/.test(s) && /\._hello\.txt/.test(s), 'AppleDouble section')
  assert(/MOVE \/config\/config\/example-sparql\/\.remote_sparql\.txt\.sb-1234 -> \/config\/config\/example-sparql\/remote_sparql\.txt/.test(s), 'config save sequence')
})
await check('results: final-tree.md shows ._hello.txt added and nothing else changed', async () => {
  const s = read('final-tree.md')
  assert(/added `"\._hello\.txt"`/.test(s), 'no added ._hello.txt')
  assert(!/^- removed /m.test(s), 'unexpected removal')
  assert((s.match(/^- added /mg) || []).length === 1, 'more than one added path')
})

if (failed === 0) rmSync(out, { recursive: true, force: true })
else console.log(`selftest: results kept in ${out}`)
console.log(`webdav desktop harness: ${passed} pass, ${failed} fail, ${xfailed} xfail, 0 skipped (out of ${passed + failed + xfailed})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
