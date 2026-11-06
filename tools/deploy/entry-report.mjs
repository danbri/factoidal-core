#!/usr/bin/env node
// entry-report.mjs base.wasm link.map entries.json: function-level against file-level closures.
// entries.json: [{ "name": "parse Turtle", "symbols": ["..."], "module": "L4Factoidal.Syntax.Turtle" }]
// Run on a link of the lazy C (lean-c-shake --mode lazy): each constant then belongs to the
// functions that read it, so reach() is exact and needs no list of initialisers.
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { parseWasm, buildGraph, reach, summarise } from './wasm-refgraph.mjs';
const [base, map, entriesFile, leanDir] = process.argv.slice(2);
const w = parseWasm(readFileSync(base)), g = buildGraph(w);
const idx = new Map(); g.nodes.forEach((n, i) => { if (!idx.has(n.name)) idx.set(n.name, i); });
// Bytes of each object in the link, from wasm-ld -Map (code rows only).
const objBytes = new Map(); let sec = '';
for (const l of readFileSync(map, 'utf8').split('\n')) {
  const f = l.trim().split(/\s+/);
  if (f.length >= 4 && /^[A-Z]+$/.test(f[3])) sec = f[3];
  const m = l.match(/^\s+\S+\s+[0-9a-f]+\s+([0-9a-f]+)\s+(\S+\.o):\(/);
  if (m && sec === 'CODE') { const o = m[2].split('/').pop(); objBytes.set(o, (objBytes.get(o) ?? 0) + parseInt(m[1], 16)); }
}
const closure = m0 => { const seen = new Set(); const go = m => { if (seen.has(m)) return; let t; try { t = readFileSync(resolve(leanDir, m.replaceAll('.', '/') + '.lean'), 'utf8'); } catch { return; } seen.add(m); for (const x of t.matchAll(/^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)/gm)) go(x[1]); }; go(m0); return seen; };
const fix = o => o.startsWith('Core_') ? o : o;
let leanCode = 0, rest = 0; for (const [o, b] of objBytes) { if (o.startsWith('Core_')) leanCode += b; else rest += b; }
const all = summarise(g, new Uint8Array(g.nodes.length).fill(1));
const coreRest = rest;
const rows = [];
for (const e of JSON.parse(readFileSync(entriesFile, 'utf8'))) {
  const roots = e.symbols.map(s => idx.get(s)); if (roots.includes(undefined)) { console.error('missing', e.name, e.symbols.filter(s => !idx.has(s))); continue; }
  const r = summarise(g, reach(g, roots));
  let files = 0, fileBytes = 0;
  for (const m of e.module ? closure(e.module) : []) { files++; fileBytes += objBytes.get('Core_' + m.replaceAll('.', '_') + '.o') ?? 0; }
  rows.push({ entry: e.name, functions: r.functions, codeBytes: r.codeBytes, dataBytes: r.dataBytes, files, fileCodeBytes: fileBytes, fileCodeBytesWithInitRuntime: fileBytes + coreRest });
}
console.log(JSON.stringify({ link: all, leanObjectCode: leanCode, initStdRuntimeCode: coreRest, rows }, null, 0));
for (const r of rows) console.log(Object.values(r).join('\t'));
