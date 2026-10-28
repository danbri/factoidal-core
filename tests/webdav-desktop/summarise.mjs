// Summarise a request log of record-proxy.mjs as Markdown.
// https://github.com/danbri/factoidal/issues/1079
//
//   node tests/webdav-desktop/summarise.mjs RESULTS_DIR/requests.jsonl > summary.md

import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'

/** File names that clients write for their own metadata, temp files and saves. */
export const CLIENT_FILE_PATTERNS = [
  ['AppleDouble (._*), macOS', /(^|\/)\._[^/]*$/],
  ['.DS_Store, macOS Finder', /(^|\/)\.DS_Store$/],
  ['.localized / .Trashes / .fseventsd / .Spotlight-V100 / .metadata_never_index, macOS', /(^|\/)(\.localized|\.Trashes|\.fseventsd|\.Spotlight-V100|\.metadata_never_index[^/]*|\.hidden_never_index)(\/|$)/],
  ['desktop.ini / Thumbs.db / folder.jpg, Windows', /(^|\/)(desktop\.ini|Thumbs\.db|folder\.jpg)$/i],
  ['.directory, KDE', /(^|\/)\.directory$/],
  ['.Trash-*, freedesktop trash', /(^|\/)\.Trash(-\d+)?(\/|$)/],
  ['.goutputstream-*, GLib atomic save', /(^|\/)\.goutputstream-[^/]*$/],
  ['~$* / .~lock.*#, Office and LibreOffice locks', /(^|\/)(~\$[^/]*|\.~lock\.[^/]*#)$/],
  ['vim swap (.swp, .swx, 4913)', /(^|\/)(\.[^/]*\.sw[a-z]|4913)$/],
  ['backup or temp (~, .tmp, .sb-*)', /(~|\.tmp|\.TMP|(^|\/)\.sb-[^/]*)$/]
]

function lines (text) {
  return text.split('\n').filter((l) => l.trim() !== '').map((l) => JSON.parse(l))
}

function count (map, key) { map.set(key, (map.get(key) || 0) + 1) }

function destPath (rec) {
  const d = rec.reqHeaders && (rec.reqHeaders.destination || rec.reqHeaders.Destination)
  if (!d) return null
  try { return decodeURIComponent(new URL(d).pathname) } catch (_e) { return d }
}

function propNames (xml) {
  if (!xml || xml.trim() === '') return ['(no body: allprop, RFC 4918 9.1)']
  const m = /<(?:[\w.-]+:)?prop\b[^>]*>([\s\S]*?)<\/(?:[\w.-]+:)?prop>/.exec(xml)
  if (!m) return /allprop/.test(xml) ? ['(allprop)'] : /propname/.test(xml) ? ['(propname)'] : []
  const names = []
  const re = /<([\w.-]+:)?([\w.-]+)\b[^>]*?(?:xmlns(?::[\w.-]+)?="([^"]*)")?[^>]*\/?>/g
  let t
  while ((t = re.exec(m[1])) !== null) names.push(t[2])
  return names
}

/** The summary of one log, as Markdown text. */
export function summarise (records) {
  const out = []
  const agents = new Map()
  const methods = new Map()
  const statuses = new Map()
  const depths = new Map()
  const props = new Map()
  const clientFiles = new Map()
  let ms = 0
  for (const r of records) {
    count(agents, r.ua || '(none)')
    count(methods, r.method)
    count(statuses, `${r.method} ${r.status}`)
    if (r.method === 'PROPFIND') {
      count(depths, r.reqHeaders && r.reqHeaders.depth !== undefined ? r.reqHeaders.depth : '(none)')
      for (const p of propNames(r.reqBody)) count(props, p)
    }
    ms += r.ms || 0
    const written = ['PUT', 'MKCOL', 'PROPPATCH', 'LOCK', 'DELETE'].includes(r.method) ? [r.path] : []
    if (['MOVE', 'COPY'].includes(r.method)) written.push(r.path, destPath(r))
    for (const p of written) {
      if (!p) continue
      for (const [label, re] of CLIENT_FILE_PATTERNS) if (re.test(p.replace(/\/$/, ''))) { if (!clientFiles.has(label)) clientFiles.set(label, new Map()); count(clientFiles.get(label), `${r.method} ${p} -> ${r.status}`) }
    }
  }
  const table = (title, map, head) => {
    out.push(`## ${title}`, '', `| ${head} | count |`, '| --- | --- |')
    for (const [k, v] of [...map.entries()].sort((a, b) => b[1] - a[1])) out.push(`| ${String(k).replace(/\|/g, '\\|')} | ${v} |`)
    out.push('')
  }
  out.push('# WebDAV client request log summary', '')
  out.push(`${records.length} requests, ${(ms / 1000).toFixed(1)} s total server time through the proxy.`, '')
  table('Clients (User-Agent)', agents, 'User-Agent')
  table('Methods', methods, 'method')
  table('Method and status', statuses, 'method status')
  table('PROPFIND Depth header', depths, 'Depth')
  table('Properties asked for in PROPFIND bodies', props, 'property (local name)')
  out.push('## Files the client wrote for its own use', '')
  if (clientFiles.size === 0) out.push('None matched the patterns in `summarise.mjs`.', '')
  for (const [label, m] of clientFiles) {
    out.push(`### ${label}`, '')
    for (const [k, v] of [...m.entries()].slice(0, 40)) out.push(`- \`${k}\`${v > 1 ? ` (x${v})` : ''}`)
    if (m.size > 40) out.push(`- (${m.size - 40} more)`)
    out.push('')
  }
  out.push('## Requests that failed (status 400 or more, or no status)', '', 'A 404 to PROPFIND or HEAD is often a client that tests whether a name is free before it writes.', '')
  const failed = records.filter((r) => r.status === null || r.status >= 400)
  if (failed.length === 0) out.push('None.', '')
  for (const r of failed.slice(0, 80)) out.push(`- ${r.seq} \`${r.method} ${r.path}\` -> ${r.status}${r.error ? ` (${r.error})` : ''}`)
  if (failed.length > 80) out.push(`- (${failed.length - 80} more)`)
  out.push('')
  out.push('## Writes in the config tree, in order (how editors save)', '')
  const cfg = records.filter((r) => /^\/config\//.test(r.path || '') && !['GET', 'HEAD', 'PROPFIND', 'OPTIONS'].includes(r.method))
  if (cfg.length === 0) out.push('None.', '')
  for (const r of cfg.slice(0, 120)) out.push(`- ${r.seq} \`${r.method} ${r.path}${destPath(r) ? ` -> ${destPath(r)}` : ''}\` ${r.status}`)
  out.push('')
  return out.join('\n')
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const file = process.argv[2]
  if (!file) { console.error('usage: node summarise.mjs requests.jsonl'); process.exit(2) }
  process.stdout.write(summarise(lines(readFileSync(file, 'utf8'))))
}

export { lines as readLog }
