#!/usr/bin/env node
// plan-units.mjs: from a manifest and a --emit-relocs link, assign each function to a unit.
// A unit is the closure of its gate functions, less what the entries reach without passing
// a gate. A function that two units need moves to the primary. Writes the wasm-split
// manifest and prints a report. Fails when a gate is missing or is also an export. Use a link
// that Binaryen has not optimised: it inlines gates and merges identical functions.
//   node tools/deploy/plan-units.mjs deploy/units/web-render.json base.wasm --names post.wasm --out dir
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { parseWasm, buildGraph, reach, summarise } from './wasm-refgraph.mjs';
const [manifestPath, basePath, ...rest] = process.argv.slice(2);
const opt = k => { const i = rest.indexOf(k); return i < 0 ? null : rest[i + 1]; };
const m = JSON.parse(readFileSync(manifestPath, 'utf8'));
const w = parseWasm(readFileSync(basePath)); const g = buildGraph(w);
const idx = new Map(); g.nodes.forEach((n, i) => { if (!idx.has(n.name)) idx.set(n.name, i); });
const need = n => { const i = idx.get(n); if (i === undefined) throw Error('symbol not in link: ' + n); return i; };
const isInit = n => /^(runtime_|meta_)?initialize_/.test(n.name);
const gates = new Map(); for (const [u, d] of Object.entries(m.units)) for (const f of d.gate) gates.set(need(f), u);
// The primary also holds what C and the Emscripten glue call: every wasm export.
const exp = w.exports.filter(e => e.kind === 0 && e.index >= w.nImportedFuncs).map(e => e.index - w.nImportedFuncs);
const primary = reach(g, [...m.entries.map(need), ...exp], (n, i) => gates.has(i));
for (const i of gates.keys()) if (exp.includes(i)) throw Error('gate is a wasm export: ' + g.nodes[i].name);
const closures = {};
for (const [u, d] of Object.entries(m.units)) closures[u] = reach(g, d.gate.map(need), (n, i) => primary[i] === 1);
const owner = new Map(), hoisted = [];
for (const [u, s] of Object.entries(closures)) s.forEach((v, i) => { if (!v) return; if (owner.has(i)) hoisted.push(i); else owner.set(i, u); });
for (const i of hoisted) owner.delete(i);
const report = { primary: summarise(g, primary), units: {}, hoistedToPrimary: hoisted.length, total: summarise(g, new Uint8Array(g.nodes.length).fill(1)) };
for (const u of Object.keys(m.units)) { const s = new Uint8Array(g.nodes.length); owner.forEach((o, i) => { if (o === u) s[i] = 1; }); report.units[u] = summarise(g, s); }
// Names that survive in the final module.
let names = null;
if (opt('--names')) { const p = parseWasm(readFileSync(opt('--names'))); names = new Set(p.nameFn.values()); }
const out = opt('--out');
// Static inline runtime helpers have one name in many objects. A name is not an address, so a
// function whose name is not unique stays in the primary.
const nameCount = new Map(); g.nodes.forEach(n => { if (n.k === 'f') nameCount.set(n.name, (nameCount.get(n.name) ?? 0) + 1); });
if (out) {
  mkdirSync(out, { recursive: true });
  let text = '', missing = 0;
  for (const u of Object.keys(m.units)) {
    const fs = []; owner.forEach((o, i) => { if (o === u && g.nodes[i].k === 'f') { if (nameCount.get(g.nodes[i].name) > 1) { report.ambiguous = (report.ambiguous ?? 0) + 1; return; } if (!names || names.has(g.nodes[i].name)) fs.push(g.nodes[i].name); else missing++; } });
    text += u + '\n' + fs.join('\n') + '\n\n';
    report.units[u].splitFunctions = fs.length;
  }
  report.gone = missing;
  writeFileSync(out + '/split.manifest', text.trimEnd() + '\n');
  writeFileSync(out + '/plan.json', JSON.stringify(report, null, 1));
}
console.log(JSON.stringify(report, null, 1));
