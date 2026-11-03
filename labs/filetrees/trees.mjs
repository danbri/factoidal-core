// File trees to serve over WebDAV to desktop file browsers.
// https://github.com/danbri/factoidal/issues/1079 (checks with real file browsers)
//
// Each tree is one mount of `factoidal webdav-serve`. A tree is a list of
// entries { path, data } (a file) or { path, dir: true } (an empty folder).
// `path` is relative to the mount and uses `/`. `data` is a string (written
// as UTF-8) or a Uint8Array.
//
// The entries are made in memory, not read from a checkout, because some of
// them cannot exist in a git tree or on every local file system: names that
// differ only by Unicode normalisation (one file on APFS), names that Windows
// refuses (`CON.txt`, `a:b.txt`), a name with a carriage return (`Icon\r`),
// and files of 51 MB. The seeder (`tests/webdav-desktop/seed.mjs`) uploads
// them with MKCOL and PUT and records each status, so a name the server
// refuses is a result, not a crash.
//
// This file makes no protocol decision (labs/README.md rule 1).

import { createHash } from 'node:crypto'
import { deflateSync } from 'node:zlib'
import { readFileSync, readdirSync, statSync } from 'node:fs'
import { join, relative, sep } from 'node:path'
import { fileURLToPath } from 'node:url'

const STATIC_DIR = fileURLToPath(new URL('./static/', import.meta.url))

/** The committed text fixtures of one tree, as entries. */
function staticEntries (tree) {
  const root = join(STATIC_DIR, tree)
  const out = []
  const walk = (dir) => {
    for (const name of readdirSync(dir).sort()) {
      const full = join(dir, name)
      if (statSync(full).isDirectory()) walk(full)
      else out.push({ path: relative(root, full).split(sep).join('/'), data: readFileSync(full) })
    }
  }
  walk(root)
  return out
}

/** Replace `{{ORIGIN}}` and `{{MOUNT}}` in a text fixture. */
function fill (entry, ctx, mount) {
  if (!/\.(html|webloc|url|desktop|txt|md|log)$/.test(entry.path)) return entry
  const text = Buffer.from(entry.data).toString('utf8')
  if (!text.includes('{{')) return entry
  return { path: entry.path, data: text.split('{{ORIGIN}}').join(ctx.origin).split('{{MOUNT}}').join(mount) }
}

// ---------------------------------------------------------------- generators

const CRC_TABLE = (() => {
  const t = new Uint32Array(256)
  for (let n = 0; n < 256; n++) {
    let c = n
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1)
    t[n] = c >>> 0
  }
  return t
})()

function crc32 (bytes) {
  let c = 0xffffffff
  for (let i = 0; i < bytes.length; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8)
  return (c ^ 0xffffffff) >>> 0
}

function pngChunk (type, body) {
  const len = Buffer.alloc(4)
  len.writeUInt32BE(body.length)
  const tb = Buffer.concat([Buffer.from(type, 'ascii'), body])
  const crc = Buffer.alloc(4)
  crc.writeUInt32BE(crc32(tb))
  return Buffer.concat([len, tb, crc])
}

/** A 240 x 160 RGB PNG: a bar chart with fixed values, so a thumbnail is easy to recognise. */
export function barChartPng (values = [3, 7, 4, 9, 6, 2, 8]) {
  const w = 240
  const h = 160
  const raw = Buffer.alloc((w * 3 + 1) * h)
  const max = Math.max(...values)
  const barW = Math.floor(w / values.length)
  for (let y = 0; y < h; y++) {
    const row = y * (w * 3 + 1)
    raw[row] = 0
    for (let x = 0; x < w; x++) {
      const i = Math.min(values.length - 1, Math.floor(x / barW))
      const top = h - 8 - Math.round((values[i] / max) * (h - 24))
      const inBar = y >= top && y < h - 8 && (x % barW) > 3 && (x % barW) < barW - 3
      const o = row + 1 + x * 3
      if (inBar) { raw[o] = 40 + i * 25; raw[o + 1] = 110; raw[o + 2] = 200 - i * 15 } else if (y >= h - 8) { raw[o] = 60; raw[o + 1] = 60; raw[o + 2] = 60 } else { raw[o] = 250; raw[o + 1] = 250; raw[o + 2] = 245 }
    }
  }
  const ihdr = Buffer.alloc(13)
  ihdr.writeUInt32BE(w, 0)
  ihdr.writeUInt32BE(h, 4)
  ihdr[8] = 8 // bit depth
  ihdr[9] = 2 // colour type RGB
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    pngChunk('IHDR', ihdr),
    pngChunk('IDAT', deflateSync(raw)),
    pngChunk('IEND', Buffer.alloc(0))
  ])
}

/** A one-page PDF 1.4 with one line of text; the xref offsets are computed. */
export function onePagePdf (line = 'Factoidal labs: types/document.pdf') {
  const esc = line.replace(/[\\()]/g, (c) => '\\' + c)
  const stream = `BT /F1 18 Tf 72 720 Td (${esc}) Tj ET`
  const objects = [
    '<< /Type /Catalog /Pages 2 0 R >>',
    '<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
    '<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> >> >>',
    `<< /Length ${Buffer.byteLength(stream)} >>\nstream\n${stream}\nendstream`,
    '<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>'
  ]
  let body = '%PDF-1.4\n'
  const offsets = []
  objects.forEach((o, i) => {
    offsets.push(Buffer.byteLength(body))
    body += `${i + 1} 0 obj\n${o}\nendobj\n`
  })
  const xref = Buffer.byteLength(body)
  body += `xref\n0 ${objects.length + 1}\n0000000000 65535 f \n`
  for (const off of offsets) body += `${String(off).padStart(10, '0')} 00000 n \n`
  body += `trailer\n<< /Size ${objects.length + 1} /Root 1 0 R >>\nstartxref\n${xref}\n%%EOF\n`
  return Buffer.from(body, 'latin1')
}

/** `size` bytes from a fixed seed (xorshift32), the same on every machine. */
export function patternBytes (size, seed = 0x9e3779b9) {
  const out = Buffer.alloc(size)
  let s = seed >>> 0
  let i = 0
  for (; i + 4 <= size; i += 4) {
    s ^= s << 13; s >>>= 0
    s ^= s >>> 17
    s ^= s << 5; s >>>= 0
    out.writeUInt32LE(s, i)
  }
  for (; i < size; i++) out[i] = i & 0xff
  return out
}

const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex')

// --------------------------------------------------------------------- trees

/**
 * The trees, in serving order. `about` is one line for the mount file and the
 * harness; `observe` names what to look at in each client (see
 * tests/webdav-desktop/checklist.md).
 */
export const TREES = [
  {
    name: 'types',
    title: 'File types',
    about: 'one file per common type, for thumbnails, Quick Look and preview panes',
    observe: 'thumbnail in icon view; preview (Quick Look, Explorer preview pane, GNOME Sushi); which app opens it',
    entries: () => [
      ...staticEntries('types'),
      { path: 'image.png', data: barChartPng() },
      { path: 'document.pdf', data: onePagePdf() },
      { path: 'empty.txt', data: '' }
    ]
  },
  {
    name: 'links',
    title: 'Dashboards and links',
    about: 'a static HTML dashboard and link files (.webloc, .url, .desktop) that open it over http',
    observe: 'does a double-click on each link file open the browser at the served URL; does page.html from the mount run its script',
    entries: (ctx) => staticEntries('links').map((e) => fill(e, ctx, 'links'))
  },
  {
    name: 'config',
    title: 'Configuration folders',
    about: 'config/<service>/remote_*.txt files, queries/ and results/, to watch how editors save',
    observe: 'edit and save a remote_*.txt in TextEdit, Notepad, gedit, Kate, VS Code, vim: which requests (PUT in place, or PUT temp + MOVE, or DELETE + PUT) appear in the request log',
    entries: (ctx) => staticEntries('config').map((e) => fill(e, ctx, 'config'))
  },
  {
    name: 'names',
    title: 'File names',
    about: 'names with spaces, Unicode (NFC and NFD), emoji, URL and Windows reserved characters, reserved device names, a long name, a case-only pair',
    observe: 'which names are listed, which open, which a client renames or hides; NFC/NFD pair; case pair on case-insensitive clients',
    entries: () => {
      const names = [
        'with space.txt',
        'café-nfc.txt',
        'café-nfd.txt',
        'emoji-\u{1F989}.txt',
        'hash#.txt',
        'percent%25.txt',
        'question?.txt',
        'colon:name.txt',
        'star*.txt',
        'quote".txt',
        'angle<brackets>.txt',
        'pipe|.txt',
        'trailing-dot.',
        'trailing-space ',
        'CON.txt',
        'nul.txt',
        `long-${'x'.repeat(195)}.txt`,
        'Icon\r'
      ]
      const out = names.map((n) => ({ path: n, data: `${JSON.stringify(n)}\n` }))
      out.push({ path: 'normalisation-pair/é.txt', data: 'NFC U+00E9\n' })
      out.push({ path: 'normalisation-pair/é.txt', data: 'NFD U+0065 U+0301\n' })
      out.push({ path: 'case-pair/Readme.txt', data: 'Readme.txt\n' })
      out.push({ path: 'case-pair/README.txt', data: 'README.txt\n' })
      out.push({ path: 'NAMES.txt', data: names.map((n) => JSON.stringify(n)).join('\n') + '\n' })
      return out
    }
  },
  {
    name: 'hidden',
    title: 'Hidden files and folder metadata',
    about: 'dot files, the GNOME .hidden list, Windows desktop.ini, the KDE .directory file',
    observe: 'which names each client hides; whether desktop.ini or .directory change the folder icon; which metadata files the client writes back (.DS_Store, ._*, Thumbs.db, desktop.ini)',
    entries: () => staticEntries('hidden')
  },
  {
    name: 'sizes',
    title: 'File sizes',
    about: 'files of 0 B, 1 KiB, 1 MiB, 10 MiB, 49 MB and 51 MB (Windows WebClient default limit: 50,000,000 bytes) with SHA256SUMS',
    observe: 'copy each file to local disk and check SHA256SUMS; on Windows, the 51 MB file',
    entries: () => {
      const sizes = [['zero.bin', 0], ['1KiB.bin', 1024], ['1MiB.bin', 1 << 20], ['10MiB.bin', 10 << 20], ['49MB.bin', 49000000], ['51MB.bin', 51000000]]
      const out = []
      const sums = []
      for (const [name, size] of sizes) {
        const data = patternBytes(size)
        out.push({ path: name, data })
        sums.push(`${sha256(data)}  ${name}`)
      }
      out.push({ path: 'SHA256SUMS', data: sums.join('\n') + '\n' })
      return out
    }
  },
  {
    name: 'many',
    title: 'Many files',
    about: '1,000 small files in one folder',
    observe: 'time to show the folder; does the client list all 1,000; PROPFIND count in the request log',
    entries: () => {
      const out = []
      for (let i = 1; i <= 1000; i++) {
        const n = String(i).padStart(4, '0')
        out.push({ path: `item-${n}.txt`, data: `item ${n}\n` })
      }
      return out
    }
  },
  {
    name: 'deep',
    title: 'Deep folders',
    about: '32 nested folders with one file at the bottom, and an empty folder',
    observe: 'path length limits (Windows MAX_PATH 260); does the client open the leaf',
    entries: () => {
      const parts = []
      for (let i = 1; i <= 32; i++) parts.push(`level-${String(i).padStart(2, '0')}`)
      return [
        { path: `${parts.join('/')}/leaf.txt`, data: `depth 32\n` },
        { path: 'empty-folder/', dir: true }
      ]
    }
  }
]

/** One tree by name, or throw with the list of names. */
export function treeByName (name) {
  const t = TREES.find((x) => x.name === name)
  if (!t) throw new Error(`no tree ${JSON.stringify(name)}; trees: ${TREES.map((x) => x.name).join(', ')}`)
  return t
}

/** The entries of a tree, with byte data, sorted so parents come first. */
export function materialise (tree, ctx) {
  const entries = tree.entries(ctx).map((e) => (e.dir ? e : { path: e.path, data: typeof e.data === 'string' ? Buffer.from(e.data, 'utf8') : Buffer.from(e.data) }))
  return entries.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0))
}

/** The folders a list of entries needs, parents first, each ending in `/`. */
export function foldersOf (entries) {
  const set = new Set()
  for (const e of entries) {
    const segs = e.path.split('/')
    for (let i = 1; i < segs.length; i++) {
      const f = segs.slice(0, i).join('/')
      if (f !== '') set.add(f + '/')
    }
    if (e.dir) set.add(e.path.endsWith('/') ? e.path : e.path + '/')
  }
  return [...set].sort((a, b) => a.split('/').length - b.split('/').length || (a < b ? -1 : 1))
}
