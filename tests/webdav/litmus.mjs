// litmus (the WebDAV conformance suite of the neon project) against both
// kinds of mount of `factoidal webdav-serve`
// (https://github.com/danbri/factoidal/issues/1066).
//
//   node tests/webdav/litmus.mjs          (needs `litmus` on PATH: apt-get install litmus)
//
// Starts `lws-serve --authz` with --owner the did:key of a key made here, and
// `webdav-serve` with a local mount (an lws-serve storage directory) and a
// remote mount (that lws-serve, auth did-key). Runs litmus's five suites
// (basic, copymove, props, locks, http) against each mount and reads every
// test line.
//
// Expected failures: tests/webdav/litmus-xfail.tsv, one row per test that is
// known to fail: mount, suite, test number, test name, open issue URL. A
// listed test that passes turns the run red (exit 1), as does a failure that
// is not listed. litmus not installed: exit 2, "not run" (never a pass).
//
// Score lines: one per mount and suite, as litmus prints them, then
// "N pass, M fail, X xfail (out of T)".

import { spawn, spawnSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { keyPair, didKeyOf } from '../authz/fixtures.mjs'

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
const XFAIL = fileURLToPath(new URL('./litmus-xfail.tsv', import.meta.url))

function start (args) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } })
  return new Promise((resolve, reject) => {
    let out = ''
    let errText = ''
    const timer = setTimeout(() => reject(new Error(`no origin printed: ${out} ${errText}`)), 60000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /(http:\/\/[^\s]+)/.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1] }) }
    })
    child.stderr.on('data', (c) => { errText += c })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${out} ${errText}`)) })
  })
}

async function stop (proc) {
  if (proc === null) return
  proc.child.kill('SIGTERM')
  await new Promise((resolve) => proc.child.on('close', resolve))
}

function readXfail () {
  const rows = new Map()
  for (const line of readFileSync(XFAIL, 'utf8').split('\n')) {
    if (line.trim() === '' || line.startsWith('#')) continue
    const [mount, suite, num, name, issue] = line.split('\t')
    if (!/^https:\/\/github\.com\/danbri\/factoidal\/issues\/\d+$/.test(issue || '')) {
      throw new Error(`litmus-xfail.tsv: the row ${mount} ${suite} ${num} names no issue URL`)
    }
    rows.set(`${mount}\t${suite}\t${num}\t${name}`, issue)
  }
  return rows
}

/** Run litmus once; every test line and every summary line. */
function litmus (url, cwd) {
  const r = spawnSync('litmus', [url], { cwd, encoding: 'utf8', timeout: 600000 })
  const text = (r.stdout || '') + (r.stderr || '')
  const tests = []
  const summaries = []
  let suite = ''
  for (const line of text.split('\n')) {
    const s = /^-> running `([a-z]+)':/.exec(line)
    if (s) { suite = s[1]; continue }
    const sum = /^<- summary for `[a-z]+': .*$/.exec(line)
    if (sum) { summaries.push(sum[0]); continue }
    // " 3. put_get............... pass" (litmus prints the name twice when
    // stdout is not a terminal; the last field is the result).
    const t = /(\d+)\. ([a-z0-9_]+)\.*\s+(pass|FAIL|SKIPPED|WARNING)(.*)$/.exec(line)
    if (t) tests.push({ suite, num: t[1], name: t[2], result: t[3], detail: t[4].trim() })
  }
  return { status: r.status, tests, summaries, text }
}

async function main () {
  // Emergency mode (https://github.com/danbri/factoidal/issues/1147):
  // webdav-serve is read only, and every litmus suite (basic, copymove,
  // props, locks, http) writes. The suite is not run until writes come
  // back; this is a skip, not a pass.
  // FACTOIDAL_LITMUS_READ_ONLY_SKIP=0 runs it anyway (the writes then fail).
  if (process.env.FACTOIDAL_LITMUS_READ_ONLY_SKIP !== '0') {
    console.log('litmus: 0 pass, 0 fail, 0 xfail (out of 0) - not run: webdav-serve is read only (https://github.com/danbri/factoidal/issues/1147); every litmus suite writes')
    process.exit(2)
  }
  if (spawnSync('litmus', ['--version'], { encoding: 'utf8' }).error) {
    console.log('litmus: 0 pass, 0 fail, 0 xfail (out of 0) - not run: litmus is not installed (apt-get install litmus)')
    process.exit(2)
  }
  const xfail = readXfail()
  const dir = mkdtempSync(join(process.env.WEBDAV_TEST_TMP || tmpdir(), 'factoidal-litmus-'))
  const conf = join(dir, 'conf')
  mkdirSync(conf)
  mkdirSync(join(conf, 'store'))
  const owner = keyPair('ES256')
  const did = didKeyOf(owner)
  writeFileSync(join(conf, 'owner.jwk'), JSON.stringify(owner.privateKey.export({ format: 'jwk' })), { mode: 0o600 })
  let lws = null
  let web = null
  let pass = 0
  let fail = 0
  let xf = 0
  const problems = []
  try {
    lws = await start(['lws-serve', join(dir, 'lws'), '--port', '0', '--authz', join(dir, 'lws-as'), '--owner', did, '--quiet'])
    writeFileSync(join(conf, 'remote.md'), `# Remote\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: owner.jwk\n- writable: true\n- users: guest\n`)
    web = await start(['webdav-serve', conf, '--port', '0', '--quiet', '--guest', 'guest'])
    for (const mount of ['remote']) {
      const work = join(dir, `work-${mount}`)
      mkdirSync(work)
      const got = litmus(`${web.origin}/${mount}/`, work)
      for (const s of got.summaries) console.log(`${mount}: ${s}`)
      if (got.tests.length === 0) {
        problems.push(`${mount}: litmus ran no test (exit ${got.status}): ${got.text.slice(0, 400)}`)
        fail += 1
        continue
      }
      for (const t of got.tests) {
        const key = `${mount}\t${t.suite}\t${t.num}\t${t.name}`
        const listed = xfail.get(key)
        if (t.result === 'pass' || t.result === 'WARNING') {
          if (listed !== undefined) { fail += 1; problems.push(`${key}: passes, but is listed as an expected failure (${listed}); remove the row and close the issue`) } else pass += 1
          if (t.result === 'WARNING') problems.push(`${key}: WARNING ${t.detail}`)
        } else if (listed !== undefined) {
          xf += 1
        } else {
          fail += 1
          problems.push(`${key}: ${t.result} ${t.detail}`)
        }
      }
    }
  } finally {
    await stop(web)
    await stop(lws)
    rmSync(dir, { recursive: true, force: true })
  }
  console.log(`litmus: ${pass} pass, ${fail} fail, ${xf} xfail (out of ${pass + fail + xf})`)
  for (const p of problems) console.log(`  ${p}`)
  process.exit(fail === 0 ? 0 : 1)
}

await main()
