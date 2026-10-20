#!/usr/bin/env node
// tools/stamp-l4-version.mjs BUILD_INFO_JSON [RELEASE_TAG]
//
// Write npm/factoidal/l4-assets/version.json (and npm/factoidal-lean/
// version.json, when that copy of the wasm is installed) from the
// danbri/factoidal-builds release that built the installed wasm.
// tools/fetch-builds.sh --set web calls this after it has verified every
// file of the release against build-info.json.
//
// Every value comes from the release or from the installed files:
//   gitSha, builtAt, leanToolchain, emscripten  <- build-info.json
//   wasmSha256/Bytes, coreWasmSha256/Bytes      <- the installed files,
//                                                  checked against build-info.json
//   engineVersion                               <- version() of the loaded wasm
// The members `engine`, `note` and `claims` of the committed placeholder
// are kept. The member names are the ones formal/lean4/Wasm/build-wasm.sh
// step 9 writes for a local build. Exit 1 when an installed file differs
// from build-info.json; nothing is written then.

import { createHash } from 'node:crypto'
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

const [infoPath, tagArg] = process.argv.slice(2)
if (!infoPath) {
  console.error('usage: stamp-l4-version.mjs BUILD_INFO_JSON [RELEASE_TAG]')
  process.exit(2)
}
const root = join(dirname(fileURLToPath(import.meta.url)), '..')
const info = JSON.parse(readFileSync(infoPath, 'utf8'))
const listed = info.artifacts['web.tar.gz'].files
const tag = tagArg || `build-${info.source_commit.slice(0, 12)}-web`

function fileFacts (rel) {
  const bytes = readFileSync(join(root, rel))
  const sha256 = createHash('sha256').update(bytes).digest('hex')
  const entry = listed[rel]
  if (!entry || entry.sha256 !== sha256 || entry.size !== bytes.length) {
    throw new Error(`${rel}: installed ${sha256} (${bytes.length} bytes) is not the file ` +
      `build-info.json lists (${entry ? entry.sha256 + ', ' + entry.size + ' bytes' : 'not listed'})`)
  }
  return { sha256, bytes: bytes.length }
}

async function engineVersion (assetsDir) {
  const loader = await import(pathToFileURL(join(assetsDir, 'l4factoidal.js')).href)
  return (await loader.loadL4()).version()
}

const tc = info.toolchains || {}
const leanMatch = /version (\d+\.\d+\.\d+)/.exec(tc.lean || '')
const provenance = {
  stamped: true,
  release: `danbri/factoidal-builds ${tag}`,
  releaseRun: info.run_url,
  gitSha: info.source_commit,
  builtAt: info.built_at,
  leanToolchain: leanMatch ? `leanprover/lean4:v${leanMatch[1]}` : (tc.lean || null),
  emscripten: tc.emscripten || null,
  abiVersion: '1'
}

const targets = [
  { dir: 'npm/factoidal/l4-assets', core: true },
  { dir: 'npm/factoidal-lean', core: false }
]
let wrote = 0
for (const t of targets) {
  const wasmRel = `${t.dir}/l4factoidal.wasm`
  if (!existsSync(join(root, wasmRel))) continue
  const full = fileFacts(wasmRel)
  const core = t.core ? fileFacts(`${t.dir}/l4factoidal-core.wasm`) : null
  const version = await engineVersion(join(root, t.dir))
  const path = join(root, t.dir, 'version.json')
  let old = {}
  try { old = JSON.parse(readFileSync(path, 'utf8')) } catch (_e) { old = {} }
  const out = {}
  if (old.engine) out.engine = old.engine
  if (old.note) out.note = old.note
  Object.assign(out, provenance, {
    engineVersion: version,
    version,
    wasmSha256: full.sha256,
    wasmBytes: full.bytes
  })
  if (core) {
    out.coreWasmSha256 = core.sha256
    out.coreWasmBytes = core.bytes
  }
  if (old.claims) out.claims = old.claims
  writeFileSync(path, JSON.stringify(out, null, 2) + '\n')
  console.error(`stamp-l4-version: ${t.dir}/version.json <- ${tag} (wasm ${full.sha256.slice(0, 12)}, engine ${version})`)
  wrote += 1
}
if (wrote === 0) {
  console.error('stamp-l4-version: no installed l4factoidal.wasm; nothing stamped')
  process.exit(1)
}
