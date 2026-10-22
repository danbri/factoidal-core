// Scaling assertion for one LWS PUT and one GET of an N-Triples body
// through the `lws-serve` host (https://github.com/danbri/factoidal/issues/903).
//
//   node tests/lws/scaling.mjs [--base N]      (default N = 25000 triples)
//
// Each size n, 2n, 4n runs in its own Node process with a fresh engine: one
// PUT (201), one more PUT of the same body (204, the path that compares the
// existing resource's entity tag), one GET. The GET must return the PUT body
// byte for byte. Per size the row keeps the minimum of three runs of each
// request, and the peak resident set of the child process.
//
// Bounds (skills/danbri-function-precrime-checkers, "the scaling
// assertion"), with the model and the defect's ratio:
//   time(4n) <= 6.0 * max(time(n), 50 ms) for PUT and for GET. The model is
//     linear in the body bytes (ratio 4); a quadratic defect gives 16. The
//     50 ms floor keeps timer noise on a fast baseline out of the verdict.
//   rss(4n) - rss(n) <= 24 * (bytes(4n) - bytes(n)) + 64 MiB. The body is
//     held by the host string, the request buffer, the engine's ByteArray
//     and the response; the wasm memory does not shrink. Before the repair
//     a 100,000-triple GET stopped the engine with out of memory.
//   Absolute: PUT and GET of the 4n body each under 2 s (the issue's target
//     at 100,000 triples).
//
// The type index (https://github.com/danbri/factoidal/issues/912): a store of
// m, 2m, 4m data resources (default m = 500, `--index-base M`), each created
// with a Link rel=type; every tenth resource also has a type of its own
// group, so a search for one rare type matches 10 resources at every size.
//   time(4m) <= 6.0 * max(time(m), 50 ms) for that search, for a search with
//     no filter (first page of the whole store), and for reopening the
//     storage from DIR/lws-state.json (the index rebuilt in one pass,
//     `TypeIndex.rebuildEntries`). The models are linear or better; a search
//     that rescanned and re-derived every resource per candidate would be
//     quadratic (16).
//   Absolute: each of the three under 2 s at 4m.
//
// The Merkle hashes (https://github.com/danbri/factoidal/issues/919, option
// `merkle`, off by default): a store of k, 2k, 4k data resources in ONE
// container (default k = 500, `--merkle-base K`), the worst case for the
// hashes, because a write recomputes the digest of every container above it
// from its member list. One repeat is 20 updates of one member (new bytes
// each time); the row keeps the minimum of three repeats, with the option on
// and off (the off figure is reported, not bounded). Then the storage is
// reopened from its snapshot with the option on (the hashes are rebuilt in
// one pass; none is stored), minimum of three.
//   time(4k) <= 6.0 * max(time(k), 50 ms) for the 20 updates with the option
//     on, and for the reopen. The model is linear in the members of the
//     container (ratio 4); a write that rebuilt every digest of the store, or
//     a reopen that hashed each container once per member, would be
//     quadratic (16).
//   Absolute: the 20 updates and the reopen each under 2 s at 4k.
//
// The cost of one write against the size of the storage
// (https://github.com/danbri/factoidal/issues/918, `--storage files`): a
// storage of s, 2s, 4s data resources (default s = 1,000, `--storage-base S`),
// opened from DIR in each mode; 20 PUTs of new small resources per repeat,
// the minimum of three repeats, per PUT; peak RSS of the child reported.
//   time(4s) <= 1.5 * time(s) with `--storage files`. The model is constant
//     (one body file and one journal record per write); the snapshot mode,
//     which writes the whole storage, gives about 4 and is reported, not
//     bounded.
//
// Score line: "N pass, M fail (out of T)". Exit 0 pass, 1 fail, 2 setup error.

import { execFileSync } from 'node:child_process'
import { existsSync, mkdtempSync, rmSync } from 'node:fs'
import { join } from 'node:path'
import { tmpdir } from 'node:os'
import { fileURLToPath } from 'node:url'

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const PKG = join(ROOT, 'npm/factoidal')
const args = process.argv.slice(2)
const opt = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined }
const EX = 'http://example.org/'

function genNTriples (n) {
  const out = []
  for (let i = 0; i < n; i++) {
    const s = `<${EX}s${Math.floor(i / 20)}>`
    const p = `<${EX}p${i % 20}>`
    let o
    switch (i % 5) {
      case 0: o = `<${EX}o${i}>`; break
      case 1: o = `"value ${i}"`; break
      case 2: o = `"label ${i}"@en`; break
      case 3: o = `"${i}"^^<http://www.w3.org/2001/XMLSchema#integer>`; break
      default: o = `_:b${i}`
    }
    out.push(`${s} ${p} ${o} .`)
  }
  return out.join('\n') + '\n'
}

async function child (n) {
  const f = await import(join(PKG, 'index.mjs'))
  const { listen } = await import(join(PKG, 'lws/server.mjs'))
  const nt = genNTriples(n)
  const bytes = Buffer.byteLength(nt)
  const lws = await listen({ engine: await f.loadEngine(), port: 0, insecureNoAuth: true, onError: () => {} })
  const url = `${lws.origin}/data.nt`
  const time = async (fn) => { const t0 = process.hrtime.bigint(); await fn(); return Number(process.hrtime.bigint() - t0) / 1e6 }
  const put = async (want) => {
    const r = await fetch(url, { method: 'PUT', headers: { 'content-type': 'application/n-triples' }, body: nt })
    await r.arrayBuffer()
    if (want !== undefined && r.status !== want) throw new Error(`PUT answered ${r.status}, expected ${want}`)
    if (r.status >= 300) throw new Error(`PUT answered ${r.status}`)
  }
  let same = true
  const get = async () => {
    const r = await fetch(url, { headers: { accept: 'application/n-triples' } })
    const b = Buffer.from(await r.arrayBuffer())
    if (r.status !== 200) throw new Error(`GET answered ${r.status}`)
    if (!b.equals(Buffer.from(nt))) same = false
  }
  try {
    const putMs = [await time(() => put(201))]
    for (let i = 0; i < 2; i++) putMs.push(await time(() => put(204)))
    const getMs = []
    for (let i = 0; i < 3; i++) getMs.push(await time(get))
    process.stdout.write(JSON.stringify({ n, bytes, put: Math.min(...putMs), get: Math.min(...getMs), same,
      rss: process.resourceUsage().maxRSS * 1024 }) + '\n')
  } finally {
    await lws.close()
  }
}

async function indexChild (m) {
  const f = await import(join(PKG, 'index.mjs'))
  const { listen } = await import(join(PKG, 'lws/server.mjs'))
  const engine = await f.loadEngine()
  const dir = mkdtempSync(join(tmpdir(), 'lws912-index-scaling-'))
  const time = async (fn) => { const t0 = process.hrtime.bigint(); await fn(); return Number(process.hrtime.bigint() - t0) / 1e6 }
  const search = (origin, filter) => fetch(`${origin}/.well-known/lws-type-search`, {
    method: 'QUERY', headers: { 'content-type': 'application/lws-query+json' }, body: JSON.stringify(filter)
  })
  try {
    const first = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {}, dir })
    const o = first.origin
    try {
      const mk = await fetch(`${o}/items/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' })
      await mk.text()
      for (let i = 0; i < m; i++) {
        const types = [`<${EX}T${i % 7}>; rel="type"`]
        if (i % (m / 10) === 0) types.push(`<${EX}Rare>; rel="type"`)
        const r = await fetch(`${o}/items/`, { method: 'POST', headers: { 'content-type': 'text/plain', slug: `r${i}`, link: types.join(', ') }, body: `resource ${i}` })
        await r.arrayBuffer()
        if (r.status !== 201) throw new Error(`POST ${i} answered ${r.status}`)
      }
      const rareMs = []
      let rareCount = -1
      for (let k = 0; k < 3; k++) {
        rareMs.push(await time(async () => {
          const r = await search(o, { type: [`${EX}Rare`] })
          rareCount = (await r.json()).totalItems
        }))
      }
      const allMs = []
      let allCount = -1
      for (let k = 0; k < 3; k++) {
        allMs.push(await time(async () => {
          const r = await search(o, {})
          allCount = (await r.json()).totalItems
        }))
      }
      if (rareCount !== 10) throw new Error(`the rare type matched ${rareCount}, expected 10`)
      if (allCount !== m + 2) throw new Error(`the whole store has ${allCount} resources, expected ${m + 2}`)
      await first.close()
      // Minimum of three reopens, as for the other rows: at m = 500 one
      // reopen takes about 45 ms, and on 2026-10-21 one sample under
      // machine load put the 4m/m ratio over its bound of 6.0 while three
      // runs alone gave 4.2 to 5.0. A reopen and a search write nothing,
      // so the repeats measure the same work.
      let reopenCount = -1
      const reopenMs = []
      for (let k = 0; k < 3; k++) {
        reopenMs.push(await time(async () => {
          const second = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {}, dir, baseIri: `${o}/` })
          try {
            const r = await search(second.origin, { type: [`${EX}Rare`] })
            reopenCount = (await r.json()).totalItems
          } finally {
            await second.close()
          }
        }))
        if (reopenCount !== 10) throw new Error(`after reopening the rare type matched ${reopenCount}`)
      }
      process.stdout.write(JSON.stringify({ m, rare: Math.min(...rareMs), all: Math.min(...allMs), reopen: Math.min(...reopenMs) }) + '\n')
    } catch (e) {
      await first.close().catch(() => {})
      throw e
    }
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

async function merkleChild (k) {
  const f = await import(join(PKG, 'index.mjs'))
  const { listen } = await import(join(PKG, 'lws/server.mjs'))
  const { writeSnapshot } = await import(join(PKG, 'lws/persist.mjs'))
  const engine = await f.loadEngine()
  const time = async (fn) => { const t0 = process.hrtime.bigint(); await fn(); return Number(process.hrtime.bigint() - t0) / 1e6 }
  const row = { k }
  for (const merkle of [true, false]) {
    const s = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {}, merkle })
    const o = s.origin
    try {
      const mk = await fetch(`${o}/items/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' })
      await mk.text()
      for (let i = 0; i < k; i++) {
        const r = await fetch(`${o}/items/`, { method: 'POST', headers: { 'content-type': 'text/plain', slug: `r${i}` }, body: `resource ${i}` })
        await r.arrayBuffer()
        if (r.status !== 201) throw new Error(`POST ${i} answered ${r.status}`)
      }
      let n = 0
      const writes = []
      for (let rep = 0; rep < 3; rep++) {
        writes.push(await time(async () => {
          for (let j = 0; j < 20; j++) {
            const r = await fetch(`${o}/items/r${k >> 1}`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: `update ${n++}` })
            await r.arrayBuffer()
            if (r.status !== 204) throw new Error(`PUT answered ${r.status}`)
          }
        }))
      }
      const head = await fetch(`${o}/items/`, { method: 'HEAD' })
      await head.arrayBuffer()
      const root = head.headers.get('factoidal-merkle-root')
      if (merkle && root === null) throw new Error('no Factoidal-Merkle-Root with merkle on')
      if (!merkle && root !== null) throw new Error('a Factoidal-Merkle-Root with merkle off')
      row[merkle ? 'writeOn' : 'writeOff'] = Math.min(...writes)
      if (merkle) {
        // Reopen from the snapshot of this storage, with the option on.
        const dir = mkdtempSync(join(tmpdir(), 'lws919-merkle-scaling-'))
        try {
          const storage = await s.storage()
          const answer = engine.call('lwsSnapshot', [storage.handle])
          writeSnapshot(dir, answer.snapshot)
          const reopen = []
          for (let rep = 0; rep < 3; rep++) {
            reopen.push(await time(async () => {
              const t = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {}, merkle: true, dir, baseIri: `${o}/` })
              try {
                const h = await fetch(`${t.origin}/items/`, { method: 'HEAD' })
                await h.arrayBuffer()
                if (h.headers.get('factoidal-merkle-root') !== root) throw new Error('the reopened root differs')
              } finally { await t.close() }
            }))
          }
          row.reopen = Math.min(...reopen)
        } finally {
          rmSync(dir, { recursive: true, force: true })
        }
      }
    } finally {
      await s.close()
    }
  }
  process.stdout.write(JSON.stringify(row) + '\n')
}

if (opt('--child')) {
  await child(Number(opt('--child')))
  process.exit(0)
}
if (opt('--index-child')) {
  await indexChild(Number(opt('--index-child')))
  process.exit(0)
}
// The cost of one write against the size of the storage
// (https://github.com/danbri/factoidal/issues/918). A storage of s data
// resources is built in memory, written as lws-state.json, and opened from
// DIR in the given mode (`files` migrates it). One repeat is 20 PUTs of new
// small resources; the row keeps the minimum of three repeats, per PUT, and
// the peak resident set of the child process.
async function storageChild (s, mode) {
  const f = await import(join(PKG, 'index.mjs'))
  const { listen } = await import(join(PKG, 'lws/server.mjs'))
  const { writeSnapshot } = await import(join(PKG, 'lws/persist.mjs'))
  const engine = await f.loadEngine()
  const time = async (fn) => { const t0 = process.hrtime.bigint(); await fn(); return Number(process.hrtime.bigint() - t0) / 1e6 }
  const dir = mkdtempSync(join(tmpdir(), 'lws918-storage-scaling-'))
  try {
    const fill = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {} })
    const o = fill.origin
    try {
      const mk = await fetch(`${o}/items/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' })
      await mk.text()
      for (let i = 0; i < s; i++) {
        const r = await fetch(`${o}/items/`, { method: 'POST', headers: { 'content-type': 'text/plain', slug: `r${i}` }, body: `resource ${i} `.repeat(20) })
        await r.arrayBuffer()
        if (r.status !== 201) throw new Error(`POST ${i} answered ${r.status}`)
      }
      const storage = await fill.storage()
      writeSnapshot(dir, engine.call('lwsSnapshot', [storage.handle]).snapshot)
    } finally { await fill.close() }
    const server = await listen({ engine, port: 0, insecureNoAuth: true, onError: () => {}, dir, baseIri: `${o}/`, storage: mode })
    const reps = []
    let k = 0
    try {
      for (let rep = 0; rep < 3; rep++) {
        reps.push(await time(async () => {
          for (let j = 0; j < 20; j++) {
            const r = await fetch(`${server.origin}/items/new${k++}`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: `new ${k}` })
            await r.arrayBuffer()
            if (r.status !== 201) throw new Error(`PUT answered ${r.status}`)
          }
        }) / 20)
      }
    } finally { await server.close() }
    process.stdout.write(JSON.stringify({ s, mode, put: Math.min(...reps), rss: process.resourceUsage().maxRSS * 1024 }) + '\n')
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

if (opt('--merkle-child')) {
  await merkleChild(Number(opt('--merkle-child')))
  process.exit(0)
}
if (opt('--storage-child')) {
  await storageChild(Number(opt('--storage-child')), opt('--mode'))
  process.exit(0)
}

if (!existsSync(join(PKG, 'l4-assets/l4factoidal.wasm'))) {
  console.error('lws scaling: npm/factoidal/l4-assets/l4factoidal.wasm missing (tools/fetch-builds.sh --set web)')
  process.exit(2)
}
const base = Number(opt('--base') ?? 25000)
const rows = []
for (const n of [base, 2 * base, 4 * base]) {
  let out
  try {
    out = execFileSync(process.execPath, [fileURLToPath(import.meta.url), '--child', String(n)],
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'], timeout: 300000 })
  } catch (e) {
    console.log(`  FAIL  size ${n}: the child process stopped (${String(e.message).split('\n')[0]})`)
    console.log('lws scaling: 0 pass, 1 fail (out of 1)')
    process.exit(1)
  }
  const r = JSON.parse(out.trim().split('\n').pop())
  rows.push(r)
  console.log(`  size ${n}: ${r.bytes} bytes, PUT ${r.put.toFixed(1)} ms, GET ${r.get.toFixed(1)} ms, ` +
              `peak RSS ${(r.rss / 1048576).toFixed(1)} MiB`)
}

let pass = 0
let fail = 0
const check = (name, ok, detail) => {
  if (ok) pass++; else fail++
  console.log(`  ${ok ? 'ok   ' : 'FAIL '} ${name} (${detail})`)
}
const [a, , c] = rows
for (const op of ['put', 'get']) {
  const ratio = c[op] / Math.max(a[op], 50)
  check(`${op.toUpperCase()} time 4n/n <= 6.0`, ratio <= 6.0, `ratio ${ratio.toFixed(2)}`)
  check(`${op.toUpperCase()} at ${c.n} triples < 2000 ms`, c[op] < 2000, `${c[op].toFixed(1)} ms`)
}
const memBound = 24 * (c.bytes - a.bytes) + 64 * 1048576
check('peak RSS growth n to 4n <= 24 bytes per body byte + 64 MiB', c.rss - a.rss <= memBound,
      `${((c.rss - a.rss) / 1048576).toFixed(1)} MiB, bound ${(memBound / 1048576).toFixed(1)} MiB`)
check('GET returns the PUT body byte for byte at every size', rows.every((r) => r.same), rows.map((r) => r.same).join(','))

// The type index (issue 912).
const mBase = Number(opt('--index-base') ?? 500)
const irows = []
for (const m of [mBase, 2 * mBase, 4 * mBase]) {
  let out
  try {
    out = execFileSync(process.execPath, [fileURLToPath(import.meta.url), '--index-child', String(m)],
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'], timeout: 600000 })
  } catch (e) {
    check(`type index at ${m} resources`, false, `the child process stopped (${String(e.message).split('\n')[0]})`)
    break
  }
  const r = JSON.parse(out.trim().split('\n').pop())
  irows.push(r)
  console.log(`  index ${m} resources: rare-type search ${r.rare.toFixed(1)} ms, whole-store search ${r.all.toFixed(1)} ms, ` +
              `reopen and search ${r.reopen.toFixed(1)} ms`)
}
if (irows.length === 3) {
  const [ia, , ic] = irows
  for (const [op, label] of [['rare', 'search for a type of 10 resources'], ['all', 'search with no filter, first page'],
    ['reopen', 'reopen from the snapshot (index rebuilt) and search']]) {
    const ratio = ic[op] / Math.max(ia[op], 50)
    check(`type index: ${label}, time 4m/m <= 6.0`, ratio <= 6.0, `ratio ${ratio.toFixed(2)}`)
    check(`type index: ${label} at ${ic.m} resources < 2000 ms`, ic[op] < 2000, `${ic[op].toFixed(1)} ms`)
  }
}
// The Merkle hashes (issue 919).
const kBase = Number(opt('--merkle-base') ?? 500)
const mrows = []
for (const k of [kBase, 2 * kBase, 4 * kBase]) {
  let out
  try {
    out = execFileSync(process.execPath, [fileURLToPath(import.meta.url), '--merkle-child', String(k)],
      { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'], timeout: 900000 })
  } catch (e) {
    check(`merkle at ${k} members`, false, `the child process stopped (${String(e.message).split('\n')[0]})`)
    break
  }
  const r = JSON.parse(out.trim().split('\n').pop())
  mrows.push(r)
  console.log(`  merkle ${k} members in one container: 20 updates ${r.writeOn.toFixed(1)} ms on, ` +
              `${r.writeOff.toFixed(1)} ms off; reopen (hashes rebuilt) ${r.reopen.toFixed(1)} ms`)
}
if (mrows.length === 3) {
  const [ma, , mc] = mrows
  for (const [op, label] of [['writeOn', '20 updates of one member with merkle on'],
    ['reopen', 'reopen with merkle on (hashes rebuilt in one pass)']]) {
    const ratio = mc[op] / Math.max(ma[op], 50)
    check(`merkle: ${label}, time 4k/k <= 6.0`, ratio <= 6.0, `ratio ${ratio.toFixed(2)}`)
    check(`merkle: ${label} at ${mc.k} members < 2000 ms`, mc[op] < 2000, `${mc[op].toFixed(1)} ms`)
  }
}
// The cost of one write with `--storage files` (issue 918).
const sBase = Number(opt('--storage-base') ?? 1000)
const srows = { snapshot: [], files: [] }
for (const mode of ['snapshot', 'files']) {
  for (const s of [sBase, 2 * sBase, 4 * sBase]) {
    let out
    try {
      out = execFileSync(process.execPath, [fileURLToPath(import.meta.url), '--storage-child', String(s), '--mode', mode],
        { encoding: 'utf8', stdio: ['ignore', 'pipe', 'inherit'], timeout: 900000 })
    } catch (e) {
      check(`storage ${mode} at ${s} resources`, false, `the child process stopped (${String(e.message).split('\n')[0]})`)
      break
    }
    const r = JSON.parse(out.trim().split('\n').pop())
    srows[mode].push(r)
    console.log(`  storage ${mode}, ${s} resources: PUT ${r.put.toFixed(2)} ms, peak RSS ${(r.rss / 1048576).toFixed(1)} MiB`)
  }
}
if (srows.files.length === 3) {
  const [fa, , fc] = srows.files
  const ratio = fc.put / fa.put
  check(`storage files: PUT time 4s/s <= 1.5 (s = ${sBase}, flat in the storage size)`, ratio <= 1.5, `ratio ${ratio.toFixed(2)}`)
}
if (srows.snapshot.length === 3) {
  const [sa, , sc] = srows.snapshot
  // Reported, not bounded: the snapshot mode writes the whole storage.
  console.log(`  storage snapshot: PUT time 4s/s ${(sc.put / sa.put).toFixed(2)} (reported; the snapshot is linear in the storage)`)
}
console.log(`lws scaling: ${pass} pass, ${fail} fail (out of ${pass + fail})`)
process.exit(fail ? 1 : 0)
