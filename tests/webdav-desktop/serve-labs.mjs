#!/usr/bin/env node
// Serve the lab file trees over WebDAV, through a recording proxy, for checks
// with desktop file browsers.
// https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
//
//   node tests/webdav-desktop/serve-labs.mjs [--port 8091] [--trees types,names]
//        [--out DIR] [--cli PATH] [--keep] [--exit-after-seed] [--duration SECONDS]
//
// What it does:
//   1. makes a temporary CONFIGDIR with one mount file per tree of
//      labs/filetrees/trees.mjs (`kind: local`, `storage: files`);
//   2. starts `factoidal webdav-serve CONFIGDIR --port 0`;
//   3. puts each tree into its mount with MKCOL and PUT, straight to the
//      server (not through the proxy), and writes seed.json;
//   4. starts the recording proxy on 127.0.0.1:PORT, and prints how to
//      connect each file browser to it;
//   5. on Ctrl-C (or after --duration): lists every mount again, writes
//      final-tree.md (what the client added or removed), summary.md (from
//      requests.jsonl), and stops the server.
//
// The engine: --cli PATH, else $FACTOIDAL_CLI, else this checkout's
// npm/factoidal/bin/factoidal.mjs when its engine assets are present
// (tools/fetch-builds.sh), else `npx -y -p @factoidal/core factoidal`.
//
// The server and the proxy listen on 127.0.0.1 only. The trees hold no
// secret, but every local process and every web page in a local browser can
// reach the port while it runs (https://github.com/danbri/factoidal/issues/1108,
// WebDAV listener login).

import { spawn } from 'node:child_process'
import { createServer as createNetServer } from 'node:net'
import { existsSync, mkdirSync, mkdtempSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import { tmpdir, platform, arch, release } from 'node:os'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TREES, treeByName, materialise, foldersOf } from '../../labs/filetrees/trees.mjs'
import { startRecordingProxy } from './record-proxy.mjs'
import { seedTree, walkMount } from './seed.mjs'
import { summarise, readLog } from './summarise.mjs'

const HERE = fileURLToPath(new URL('.', import.meta.url))
const REPO = resolve(HERE, '..', '..')

export function parseArgs (argv) {
  const o = { port: 8091, trees: null, out: null, cli: null, keep: false, exitAfterSeed: false, duration: null, quiet: false }
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    const next = () => { if (i + 1 >= argv.length) throw new Error(`${a} needs a value`); return argv[++i] }
    if (a === '--port') o.port = Number(next())
    else if (a === '--trees') o.trees = next().split(',').map((s) => s.trim()).filter(Boolean)
    else if (a === '--out') o.out = resolve(next())
    else if (a === '--cli') o.cli = resolve(next())
    else if (a === '--keep') o.keep = true
    else if (a === '--exit-after-seed') o.exitAfterSeed = true
    else if (a === '--duration') o.duration = Number(next())
    else if (a === '--quiet') o.quiet = true
    else if (a === '-h' || a === '--help') { process.stdout.write(readFileSync(fileURLToPath(import.meta.url), 'utf8').split('\n').slice(1, 30).map((l) => l.replace(/^\/\/ ?/, '')).join('\n') + '\n'); process.exit(0) } else throw new Error(`unknown argument ${a}`)
  }
  if (!Number.isInteger(o.port) || o.port < 0 || o.port > 65535) throw new Error('--port must be 0..65535')
  return o
}

/** The command that runs `factoidal`: [executable, ...leading args]. */
export function factoidalCommand (cli) {
  const chosen = cli || process.env.FACTOIDAL_CLI || null
  if (chosen) return [process.execPath, chosen]
  const repoCli = join(REPO, 'npm/factoidal/bin/factoidal.mjs')
  const assets = [join(REPO, 'npm/factoidal/l4-assets/l4factoidal.wasm'), join(REPO, 'docs/web/hub/assets/l4/l4factoidal.wasm')]
  if (existsSync(repoCli) && (assets.some(existsSync) || process.env.FACTOIDAL_L4_ASSETS)) return [process.execPath, repoCli]
  return [platform() === 'win32' ? 'npx.cmd' : 'npx', '-y', '-p', '@factoidal/core', 'factoidal']
}

/** The version in the package.json next to the CLI, or null (npx: resolved at run time). */
export function engineVersion (cmd) {
  const cli = cmd[cmd.length - 1]
  try { return JSON.parse(readFileSync(join(cli, '..', '..', 'package.json'), 'utf8')).version } catch (_e) { return null }
}

/** Start webdav-serve on CONFIGDIR; resolves { child, origin, stderr() }. */
export function startServer (configDir, cmd) {
  const [exe, ...lead] = cmd
  // Its own process group on POSIX, so stopServer reaches the node process
  // that npx starts as well as npx itself.
  const win = platform() === 'win32'
  const child = spawn(exe, [...lead, 'webdav-serve', configDir, '--port', '0'], { stdio: ['ignore', 'pipe', 'pipe'], shell: win && exe.endsWith('.cmd'), detached: !win })
  let out = ''
  let err = ''
  return new Promise((resolveStart, reject) => {
    const timer = setTimeout(() => reject(new Error(`webdav-serve printed no origin in 120 s:\n${out}\n${err}`)), 120000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /^(http:\/\/127\.0\.0\.1:\d+)\s*$/m.exec(out)
      if (m) { clearTimeout(timer); resolveStart({ child, origin: m[1], stderr: () => err }) }
    })
    child.stderr.on('data', (c) => { err += c })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`webdav-serve exited ${code}:\n${err}`)) })
  })
}

/** Stop the server and every process it started; resolves when it has exited. */
export function stopServer (child) {
  return new Promise((resolveStop) => {
    if (child.exitCode !== null || child.signalCode !== null) { resolveStop(); return }
    child.once('exit', () => resolveStop())
    const signal = (sig) => {
      try {
        if (platform() === 'win32') spawn('taskkill', ['/pid', String(child.pid), '/T', '/F'], { stdio: 'ignore' })
        else process.kill(-child.pid, sig)
      } catch (_e) { try { child.kill(sig) } catch (_e2) { /* already gone */ } }
    }
    signal('SIGTERM')
    setTimeout(() => signal('SIGKILL'), 5000).unref()
  })
}

export function connectText (origin) {
  const u = new URL(origin)
  return [
    `Connect a file browser to ${origin}/`,
    '',
    'macOS Finder:  Go > Connect to Server (Cmd-K), then ' + `${origin}/`,
    `  or: mkdir -p ~/factoidal-labs && mount_webdav -v FactoidalLabs ${origin}/ ~/factoidal-labs`,
    `  or: bash tests/webdav-desktop/probe-macos.sh ${origin}/`,
    `Windows:       net use * ${origin}/   (WebClient service must run: sc query webclient)`,
    `  or: Explorer > This PC > Map network drive > ${origin}/`,
    `  or: \\\\${u.hostname}@${u.port}\\DavWWWRoot`,
    `  or: powershell -File tests\\webdav-desktop\\probe-windows.ps1 -Origin ${origin}/`,
    `GNOME Files:   Other Locations > Connect to Server > dav://${u.host}/`,
    `  or: gio mount dav://${u.host}/   or: bash tests/webdav-desktop/probe-linux.sh ${origin}/`,
    `KDE Dolphin:   webdav://${u.host}/`,
    '',
    'Then work through tests/webdav-desktop/checklist.md. Press Ctrl-C here to stop and write the summary.'
  ].join('\n')
}

/** A TCP port on 127.0.0.1 that is free now. */
export function freePort () {
  return new Promise((resolvePort, reject) => {
    const s = createNetServer()
    s.once('error', reject)
    s.listen(0, '127.0.0.1', () => { const p = s.address().port; s.close(() => resolvePort(p)) })
  })
}

function defaultOut () {
  const stamp = new Date().toISOString().replace(/[-:]/g, '').replace(/\..*$/, '').replace('T', '-')
  return join(HERE, 'results', `${stamp}-${platform()}-${arch()}`)
}

/** Compare a mount after the session with what was seeded. */
export function treeDiff (seededPaths, finalItems) {
  const finalPaths = new Set(finalItems.map((i) => (i.collection ? i.path.replace(/\/?$/, '/') : i.path)))
  const added = [...finalPaths].filter((p) => !seededPaths.has(p)).sort()
  const removed = [...seededPaths].filter((p) => !finalPaths.has(p)).sort()
  return { added, removed }
}

export async function run (opts) {
  const trees = opts.trees ? opts.trees.map(treeByName) : TREES
  const out = opts.out || defaultOut()
  mkdirSync(out, { recursive: true })
  const config = mkdtempSync(join(tmpdir(), 'factoidal-labs-dav-'))
  for (const t of trees) {
    mkdirSync(join(config, t.name))
    writeFileSync(join(config, `${t.name}.md`), `# ${t.title}\n- kind: local\n- path: ./${t.name}\n- storage: files\n\n${t.about}\n`)
  }
  const cmd = factoidalCommand(opts.cli)
  const log = (s) => { if (!opts.quiet) console.log(s) }
  log(`serve-labs: CONFIGDIR ${config}`)
  log(`serve-labs: engine command: ${cmd.join(' ')}`)
  const server = await startServer(config, cmd)
  // The server runs in its own process group: stop it if this process ends early.
  process.once('exit', () => { if (server.child.exitCode === null) { try { if (platform() === 'win32') server.child.kill(); else process.kill(-server.child.pid, 'SIGKILL') } catch (_e) { /* gone */ } } })
  log(`serve-labs: webdav-serve at ${server.origin} (not for clients; use the proxy)`)

  // The link files name the proxy's origin, so its port is fixed before the
  // trees are made; --port 0 picks a free port first.
  const port = opts.port === 0 ? await freePort() : opts.port
  const proxyOrigin = `http://127.0.0.1:${port}`
  const seed = []
  const seeded = new Map()
  for (const t of trees) {
    const entries = materialise(t, { origin: proxyOrigin })
    const folders = foldersOf(entries)
    const results = await seedTree(server.origin, t.name, entries, folders)
    seed.push({ tree: t.name, results })
    seeded.set(t.name, new Set(results.filter((r) => r.ok).map((r) => r.path)))
    const refused = results.filter((r) => !r.ok)
    log(`serve-labs: ${t.name}: ${results.length - refused.length} of ${results.length} put${refused.length ? `; refused: ${refused.map((r) => `${JSON.stringify(r.path)} ${r.status}`).join(', ')}` : ''}`)
  }
  writeFileSync(join(out, 'seed.json'), JSON.stringify({ server: server.origin, proxy: proxyOrigin, trees: seed }, null, 1) + '\n')

  const logFile = join(out, 'requests.jsonl')
  writeFileSync(logFile, '')
  const proxy = await startRecordingProxy({ target: server.origin, port, logFile })
  writeFileSync(join(out, 'environment.json'), JSON.stringify({ platform: platform(), arch: arch(), release: release(), node: process.version, started: new Date().toISOString(), origin: proxy.origin, trees: trees.map((t) => t.name), engine: cmd.join(' '), engineVersion: engineVersion(cmd) }, null, 1) + '\n')
  log('')
  log(connectText(proxy.origin))
  log(`\nserve-labs: results in ${out}`)

  let stopping = null
  const stop = async () => {
    if (stopping) return stopping
    stopping = (async () => {
      const finalLines = ['# Mounts after the session', '', 'Paths relative to each mount. "added" were not in the seeded tree (a client made them); "removed" were seeded and are gone.', '']
      for (const t of trees) {
        try {
          const items = await walkMount(server.origin, t.name)
          const { added, removed } = treeDiff(seeded.get(t.name), items)
          finalLines.push(`## ${t.name}`, '', `${items.length} members; ${added.length} added; ${removed.length} removed.`, '')
          for (const p of added.slice(0, 100)) finalLines.push(`- added \`${JSON.stringify(p)}\``)
          for (const p of removed.slice(0, 100)) finalLines.push(`- removed \`${JSON.stringify(p)}\``)
          finalLines.push('')
        } catch (e) { finalLines.push(`## ${t.name}`, '', `listing failed: ${e.message}`, '') }
      }
      writeFileSync(join(out, 'final-tree.md'), finalLines.join('\n'))
      await proxy.close()
      writeFileSync(join(out, 'summary.md'), summarise(readLog(readFileSync(logFile, 'utf8'))))
      await stopServer(server.child)
      if (!opts.keep) rmSync(config, { recursive: true, force: true })
      log(`serve-labs: wrote summary.md and final-tree.md in ${out}`)
    })()
    return stopping
  }
  return { out, config, server, proxy, seed, stop }
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  let opts
  try { opts = parseArgs(process.argv.slice(2)) } catch (e) { console.error(`serve-labs: ${e.message}`); process.exit(2) }
  const lab = await run(opts)
  const end = async () => { await lab.stop(); process.exit(0) }
  process.on('SIGINT', end)
  process.on('SIGTERM', end)
  if (opts.exitAfterSeed) await end()
  if (opts.duration !== null) setTimeout(end, opts.duration * 1000)
}
