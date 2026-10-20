// l4-assets/version.json is either the unstamped placeholder ("stamped at
// release") or a stamp whose sha256 and size equal the installed wasm files
// (tools/stamp-l4-version.mjs). A stamp that describes another build fails,
// and so does `factoidal version` on it.
import test from 'node:test'
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { existsSync, readFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { join, dirname } from 'node:path'

const pkg = join(dirname(fileURLToPath(import.meta.url)), '..')
const stamp = JSON.parse(readFileSync(join(pkg, 'l4-assets/version.json'), 'utf8'))

test('version.json is the placeholder or matches the installed wasm', () => {
  if (stamp.stamped !== true) {
    assert.equal(stamp.status, 'stamped at release')
    for (const k of ['wasmSha256', 'wasmBytes', 'coreWasmSha256', 'coreWasmBytes', 'gitSha']) {
      assert.equal(stamp[k], undefined, `an unstamped version.json claims ${k}`)
    }
    return
  }
  for (const [file, shaKey, bytesKey] of [['l4factoidal.wasm', 'wasmSha256', 'wasmBytes']]) {
    const path = join(pkg, 'l4-assets', file)
    if (!existsSync(path)) continue
    const bytes = readFileSync(path)
    assert.equal(stamp[shaKey], createHash('sha256').update(bytes).digest('hex'), file)
    assert.equal(stamp[bytesKey], bytes.length, file)
  }
})

test('factoidal version exits 0 and prints the installed wasm sha256', () => {
  const r = spawnSync(process.execPath, [join(pkg, 'bin/factoidal.mjs'), 'version', '--json'], { encoding: 'utf8' })
  assert.equal(r.status, 0, r.stderr)
  const report = JSON.parse(r.stdout)
  assert.deepEqual(report.mismatches, [])
  if (stamp.stamped === true && report.installed.wasm) {
    assert.equal(report.stamp.wasmSha256, report.installed.wasm.sha256)
  }
})
