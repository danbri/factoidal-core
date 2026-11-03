// Resource scaling of the WebDAV request decoders, through the shipped
// WebAssembly module (the smallest stack we ship), each case in its own
// process (`skills/danbri-function-precrime-checkers`).
// https://github.com/danbri/factoidal/issues/1066
//
//   node tests/webdav/scaling.mjs
//
// Cases, each at n, 2n and 4n, the largest above any recursion a wasm stack
// holds (one frame per item would overflow it):
//   mount-lines      a mount file of N lines (free text before the list)
//   proppatch-wide   a PROPPATCH of N properties, then a PROPFIND of them
//   propfind-wide    a PROPFIND naming N properties
//   deep-value       a dead property whose value nests N elements deep:
//                    refused (400, deeper than 256 levels) without a crash
// A case passes when every size answers (no crash) and the time ratio from
// n to 4n is below MAX_RATIO (default 8: linear is 4, quadratic 16).
//
// Emergency mode (https://github.com/danbri/factoidal/issues/1147): the
// server is read only, so PROPPATCH is 403 before its body is read, and
// proppatch-wide and deep-value are skipped (not passed); the mount is an
// lws mount that lists the guest, and propfind-wide asks the root
// collection, which needs no storage.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'

const SELF = fileURLToPath(import.meta.url)
const MAX_RATIO = Number(process.env.WEBDAV_SCALING_MAX_RATIO || '8')

const CASES = {
  'mount-lines': [100000, 200000, 400000],
  'proppatch-wide': [5000, 10000, 20000],
  'propfind-wide': [5000, 10000, 20000],
  'deep-value': [25000, 50000, 100000]
}

async function runCase (name, n) {
  const { openWebdav } = await import('../../npm/factoidal/webdav/server.mjs')
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-webdav-scaling-'))
  try {
    if (name === 'proppatch-wide' || name === 'deep-value') {
      return { ok: false, skip: true, detail: 'PROPPATCH is 403 in emergency mode (https://github.com/danbri/factoidal/issues/1147): the body is not read' }
    }
    const head = name === 'mount-lines' ? 'free text\n'.repeat(n) : ''
    writeFileSync(join(dir, 'm.md'), head + '# M\n- kind: lws\n- url: http://127.0.0.1:9/\n- users: guest\n')
    const t0 = performance.now()
    const dav = await openWebdav({ configDir: dir, guest: 'guest' })
    const req = (method, target, headers, body) =>
      dav.step({ method, target, headers: [['host', 'localhost'], ...headers], body: new TextEncoder().encode(body || '') })
    let detail = ''
    if (name === 'mount-lines') {
      detail = `mounts ${dav.mounts.length}`
      if (dav.mounts.length !== 1) throw new Error(detail)
    } else {
      let r
      if (name === 'proppatch-wide') {
        let props = ''
        for (let i = 0; i < n; i += 1) props += `<Z:p${i}>v${i}</Z:p${i}>`
        r = await req('PROPPATCH', '/m/a.txt', [], `<D:propertyupdate xmlns:D="DAV:" xmlns:Z="http://z/"><D:set><D:prop>${props}</D:prop></D:set></D:propertyupdate>`)
        if (r.status !== 207) throw new Error(`PROPPATCH ${r.status}`)
        r = await req('PROPFIND', '/m/a.txt', [['depth', '0']], '')
        const text = new TextDecoder().decode(r.body)
        const count = text.split('</Z:p').length - 1
        detail = `properties read back ${count}`
        if (count !== n) throw new Error(detail)
      } else if (name === 'propfind-wide') {
        let names = ''
        for (let i = 0; i < n; i += 1) names += `<Z:q${i}/>`
        r = await req('PROPFIND', '/', [['depth', '0']], `<D:propfind xmlns:D="DAV:" xmlns:Z="http://z/"><D:prop>${names}</D:prop></D:propfind>`)
        const text = new TextDecoder().decode(r.body)
        const count = text.split('<R:q').length - 1
        detail = `404 names ${count}`
        if (r.status !== 207 || count !== n) throw new Error(`${r.status} ${detail}`)
      } else if (name === 'deep-value') {
        const value = '<Z:n>'.repeat(n) + 'leaf' + '</Z:n>'.repeat(n)
        r = await req('PROPPATCH', '/m/a.txt', [], `<D:propertyupdate xmlns:D="DAV:" xmlns:Z="http://z/"><D:set><D:prop><Z:deep>${value}</Z:deep></D:prop></D:set></D:propertyupdate>`)
        // The server refuses a body nested deeper than maxBodyDepth (256,
        // L4Factoidal/WebDAV/Xml.lean) before it parses it: 400, and the
        // handle keeps serving.
        detail = `PROPPATCH ${r.status}`
        if (r.status !== 400) throw new Error(detail)
        r = await req('PROPFIND', '/m/a.txt', [['depth', '0']], '')
        detail += `, then PROPFIND ${r.status}`
        if (r.status !== 207) throw new Error(detail)
      }
    }
    const ms = performance.now() - t0
    dav.close()
    return { ok: true, ms, detail }
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

if (process.argv[2] === '--case') {
  try {
    const r = await runCase(process.argv[3], Number(process.argv[4]))
    console.log(JSON.stringify(r))
  } catch (error) {
    console.log(JSON.stringify({ ok: false, skip: error && error.unknownOp === true, detail: String(error && error.message ? error.message : error) }))
  }
  process.exit(0)
}

let pass = 0
let fail = 0
let skipped = 0
for (const [name, sizes] of Object.entries(CASES)) {
  const rows = []
  let problem = ''
  let skip = ''
  for (const n of sizes) {
    const p = spawnSync(process.execPath, [SELF, '--case', name, String(n)], { encoding: 'utf8', timeout: 600000 })
    const line = (p.stdout || '').trim().split('\n').pop() || ''
    let r
    try { r = JSON.parse(line) } catch (_e) { r = { ok: false, detail: `no answer (exit ${p.status}, signal ${p.signal}): ${(p.stderr || '').slice(-300)}` } }
    rows.push({ n, ...r })
    if (r.skip === true) { skip = r.detail; break }
    if (!r.ok) problem = `n=${n}: ${r.detail}`
  }
  // A module built before the WebDAV ops: a skip, never a pass.
  if (skip !== '') { skipped += 1; console.log(`  skip  ${name} - ${skip}`); continue }
  const ratio = rows.length === 3 && rows[0].ok && rows[2].ok ? rows[2].ms / rows[0].ms : NaN
  for (const r of rows) console.log(`  ${name} n=${r.n}: ${r.ok ? r.ms.toFixed(0) + ' ms' : 'FAILED'} ${r.detail || ''}`)
  if (problem === '' && !(ratio < MAX_RATIO)) problem = `time ratio 4n/n ${ratio.toFixed(2)} >= ${MAX_RATIO}`
  if (problem === '') { pass += 1; console.log(`  ok    ${name} (4n/n time ratio ${ratio.toFixed(2)})`) } else { fail += 1; console.log(`  FAIL  ${name}: ${problem}`) }
}
console.log(`webdav scaling: ${pass} pass, ${fail} fail, ${skipped} skipped (out of ${pass + fail + skipped})`)
process.exit(fail === 0 ? 0 : 1)
