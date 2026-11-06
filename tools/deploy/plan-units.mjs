#!/usr/bin/env node
// plan-units.mjs: from a manifest and a --emit-relocs link, assign each function to a unit.
// A unit is the closure of its gate functions, less what the entries reach without passing
// a gate. A function that two units need moves to the primary. Writes the wasm-split
// manifest and prints a report. Fails when a gate is missing or the primary reaches past one.
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
// wasm-opt merges identical functions, so a primary function can now call a name the graph put
// in a unit. Hoist such names until no primary function calls into a unit, directly or by a
// table slot that a primary function takes the address of.
if (opt('--final')) {
  const fw = parseWasm(readFileSync(opt('--final'))); const nameOf = i => fw.nameFn.get(i);
  const finalOwner = new Map(); owner.forEach((u, i) => { if (g.nodes[i].k === 'f') finalOwner.set(g.nodes[i].name, u); });
  const calls = new Map(); const dot = readFileSync(opt('--calls'), 'utf8');
  for (const m2 of dot.matchAll(/"([^"]+)" -> "([^"]+)"/g)) { if (!calls.has(m2[1])) calls.set(m2[1], []); calls.get(m2[1]).push(m2[2]); }
  // Base slot of each function, then the function now in that slot.
  const baseSlot = new Map(); w.elemFuncs.forEach((f, s) => baseSlot.set(f - w.nImportedFuncs, s));
  const taken = new Set(); // final names whose address a primary function takes
  g.nodes.forEach((n, i) => { if (primary[i] || !owner.has(i)) for (const t of g.edges[i]) if (g.nodes[t].k === 'f' && baseSlot.has(t)) { const f = fw.elemFuncs[baseSlot.get(t)]; if (f !== undefined) taken.add(nameOf(f)); } });
  let moved = 0; const stack = [...fw.nameFn.values()].filter(n => !finalOwner.has(n)).concat([...taken]);
  const seen = new Set();
  while (stack.length) {
    const n = stack.pop(); if (seen.has(n)) continue; seen.add(n);
    if (finalOwner.has(n)) { finalOwner.delete(n); moved++; }
    for (const t of calls.get(n) ?? []) if (!seen.has(t)) stack.push(t);
  }
  report.hoistedAfterMerge = moved;
  owner.forEach((u, i) => { if (g.nodes[i].k === 'f' && !finalOwner.has(g.nodes[i].name)) owner.delete(i); });
  for (const u of Object.keys(m.units)) { const s = new Uint8Array(g.nodes.length); owner.forEach((o, i) => { if (o === u) s[i] = 1; }); report.units[u] = summarise(g, s); }
}
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
