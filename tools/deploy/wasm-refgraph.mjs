#!/usr/bin/env node
// wasm-refgraph.mjs: exact reference graph of a linked wasm built with wasm-ld --emit-relocs.
// Nodes are function and data symbols. Edges come from reloc.CODE and reloc.DATA, so an
// address taken (a Lean closure) is an edge, unlike wasm-opt --print-call-graph.
//   node tools/deploy/wasm-refgraph.mjs engine.base.wasm --out graph.json [--sections]
// Usage and meaning of the numbers: docs/20261106-deployable-modules.md
import { readFileSync, writeFileSync } from 'node:fs';

export function parseWasm(buf) {
  let p = 0;
  const u8 = () => buf[p++];
  const leb = () => { let r = 0, s = 1, b; do { b = buf[p++]; r += (b & 127) * s; s *= 128; } while (b & 128); return r; };
  const sleb = () => { let r = 0n, s = 0n, b; do { b = buf[p++]; r |= BigInt(b & 127) << s; s += 7n; } while (b & 128); if (b & 64) r |= -1n << s; return Number(r); };
  const str = () => { const n = leb(); const s = buf.toString('utf8', p, p + n); p += n; return s; };
  p = 8;
  const sections = [];
  let imports = [], exports_ = [], funcBodies = [], dataSegs = [], linking = null, relocs = [], nameFn = new Map(), nImportedFuncs = 0, startFn = null;
  while (p < buf.length) {
    const id = u8(), size = leb(), start = p, end = p + size;
    let name = null;
    if (id === 0) { name = str(); }
    sections.push({ id, name, size, start, end, payload: p });
    if (id === 2) {
      const n = leb();
      for (let i = 0; i < n; i++) {
        const m = str(), f = str(), k = u8();
        if (k === 0) { leb(); nImportedFuncs++; imports.push({ m, f, k }); }
        else if (k === 1) { u8(); const fl = u8(); leb(); if (fl & 1) leb(); imports.push({ m, f, k }); }
        else if (k === 2) { u8(); const fl = u8(); leb(); if (fl & 1) leb(); imports.push({ m, f, k }); }
        else if (k === 3) { u8(); u8(); imports.push({ m, f, k }); }
        else if (k === 4) { u8(); leb(); imports.push({ m, f, k }); }
        else throw new Error('import kind ' + k);
      }
    } else if (id === 7) {
      const n = leb();
      for (let i = 0; i < n; i++) { const nm = str(), k = u8(), idx = leb(); exports_.push({ name: nm, kind: k, index: idx }); }
    } else if (id === 8) { startFn = leb(); }
    else if (id === 10) {
      const n = leb();
      for (let i = 0; i < n; i++) { const sz = leb(); funcBodies.push({ start: p, size: sz, secOff: p - start }); p += sz; }
    } else if (id === 11) {
      const n = leb();
      for (let i = 0; i < n; i++) {
        const fl = leb();
        if (fl === 1) { /* passive */ } else { if (fl === 2) leb(); while (buf[p] !== 0x0b) { const op = u8(); if (op === 0x41) sleb(); else if (op === 0x23) leb(); else throw new Error('init op ' + op); } p++; }
        const sz = leb(); dataSegs.push({ secOff: p - start, size: sz }); p += sz;
      }
    } else if (id === 0 && name === 'linking') {
      const version = leb(); const syms = []; const segInfo = [];
      while (p < end) {
        const t = u8(), l = leb(), e = p + l;
        if (t === 8) {
          const n = leb();
          for (let i = 0; i < n; i++) {
            const kind = u8(), flags = leb(); const s = { kind, flags };
            const undefinedS = flags & 0x10, explicit = flags & 0x40;
            if (kind === 0 || kind === 2 || kind === 4 || kind === 5) { s.index = leb(); if (!undefinedS || explicit) s.name = str(); }
            else if (kind === 1) { s.name = str(); if (!undefinedS) { s.seg = leb(); s.off = leb(); s.size = leb(); } }
            else if (kind === 3) { s.section = leb(); }
            syms.push(s);
          }
        } else if (t === 5) { const n = leb(); for (let i = 0; i < n; i++) { const nm = str(); leb(); leb(); segInfo.push(nm); } }
        p = e;
      }
      linking = { version, syms, segInfo };
    } else if (id === 0 && name.startsWith('reloc.')) {
      const target = leb(), n = leb(); const list = new Array(n);
      for (let i = 0; i < n; i++) {
        const type = u8(), off = leb(), idx = leb(); let addend = 0;
        if ([3, 4, 5, 8, 9, 11, 14, 15, 16, 17, 21, 22].includes(type)) addend = sleb();
        list[i] = { type, off, idx, addend };
      }
      relocs.push({ name, target, list });
    } else if (id === 0 && name === 'name') {
      while (p < end) {
        const t = u8(), l = leb(), e = p + l;
        if (t === 1) { const n = leb(); for (let i = 0; i < n; i++) { const idx = leb(); nameFn.set(idx, str()); } }
        p = e;
      }
    }
    p = end;
  }
  return { sections, imports, exports: exports_, funcBodies, dataSegs, linking, relocs, nameFn, nImportedFuncs, startFn };
}

export function buildGraph(w) {
  // Node ids: function index => 'f' list; data symbols appended.
  const nodes = []; const fnNode = new Map(); const dataBySeg = new Map();
  const symNode = new Array(w.linking.syms.length).fill(-1);
  for (let i = 0; i < w.funcBodies.length; i++) {
    const idx = i + w.nImportedFuncs;
    fnNode.set(idx, nodes.length);
    nodes.push({ k: 'f', name: w.nameFn.get(idx) ?? 'f' + idx, size: w.funcBodies[i].size });
  }
  w.linking.syms.forEach((s, i) => {
    if (s.kind === 0) {
      const n = fnNode.get(s.index);
      if (n !== undefined) { symNode[i] = n; if (s.name) nodes[n].name = s.name; }
      else symNode[i] = -2; // import
    } else if (s.kind === 1 && s.seg !== undefined) {
      const id = nodes.length; nodes.push({ k: 'd', name: s.name, size: s.size, seg: s.seg, off: s.off });
      symNode[i] = id;
      if (!dataBySeg.has(s.seg)) dataBySeg.set(s.seg, []);
      dataBySeg.get(s.seg).push(id);
    }
  });
  for (const list of dataBySeg.values()) list.sort((a, b) => nodes[a].off - nodes[b].off);
  const edges = nodes.map(() => new Set());
  const codeSec = w.sections.findIndex(s => s.id === 10), dataSec = w.sections.findIndex(s => s.id === 11);
  const sortedBodies = w.funcBodies; // ascending secOff
  const findFn = off => { let lo = 0, hi = sortedBodies.length - 1; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (sortedBodies[m].secOff <= off) lo = m; else hi = m - 1; } return lo; };
  const findSeg = off => { let lo = 0, hi = w.dataSegs.length - 1; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (w.dataSegs[m].secOff <= off) lo = m; else hi = m - 1; } return lo; };
  const dataSymAt = (seg, off) => {
    const list = dataBySeg.get(seg); if (!list) return -1;
    let lo = 0, hi = list.length - 1; if (hi < 0) return -1;
    while (lo < hi) { const m = (lo + hi + 1) >> 1; if (nodes[list[m]].off <= off) lo = m; else hi = m - 1; }
    const n = nodes[list[lo]]; return (n.off <= off && off < n.off + Math.max(n.size, 1)) ? list[lo] : -1;
  };
  const stats = { codeRelocs: 0, dataRelocs: 0, unresolvedData: 0 };
  for (const r of w.relocs) {
    if (r.target === codeSec) {
      for (const e of r.list) {
        if (e.type === 6 || e.type === 7 || e.type === 10) continue;
        stats.codeRelocs++;
        const from = findFn(e.off), to = symNode[e.idx];
        if (to < 0) continue;
        const src = fnNode.get(from + w.nImportedFuncs);
        const s = w.linking.syms[e.idx];
        let tgt = to;
        if (s.kind === 1) { const d = dataSymAt(s.seg, s.off + e.addend); if (d >= 0) tgt = d; }
        edges[src].add(tgt);
      }
    } else if (r.target === dataSec) {
      for (const e of r.list) {
        stats.dataRelocs++;
        const seg = findSeg(e.off), off = e.off - w.dataSegs[seg].secOff;
        const src = dataSymAt(seg, off);
        if (src < 0) { stats.unresolvedData++; continue; }
        const to = symNode[e.idx]; if (to < 0) continue;
        const s = w.linking.syms[e.idx]; let tgt = to;
        if (s.kind === 1) { const d = dataSymAt(s.seg, s.off + e.addend); if (d >= 0) tgt = d; }
        edges[src].add(tgt);
      }
    }
  }
  return { nodes, edges: edges.map(s => [...s]), stats };
}

export function reach(g, roots, skip = () => false) {
  const seen = new Uint8Array(g.nodes.length); const stack = [];
  for (const r of roots) if (!seen[r]) { seen[r] = 1; stack.push(r); }
  while (stack.length) { const n = stack.pop(); for (const t of g.edges[n]) if (!seen[t] && !skip(g.nodes[t], t)) { seen[t] = 1; stack.push(t); } }
  return seen;
}

export function summarise(g, seen) {
  let f = 0, fb = 0, d = 0, db = 0;
  g.nodes.forEach((n, i) => { if (seen[i]) { if (n.k === 'f') { f++; fb += n.size; } else { d++; db += n.size; } } });
  return { functions: f, codeBytes: fb, dataSymbols: d, dataBytes: db };
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const [file, ...rest] = process.argv.slice(2);
  const w = parseWasm(readFileSync(file));
  const names = { 1: 'type', 2: 'import', 3: 'function', 4: 'table', 5: 'memory', 6: 'global', 7: 'export', 8: 'start', 9: 'elem', 10: 'code', 11: 'data', 12: 'datacount', 13: 'tag' };
  for (const s of w.sections) console.log((s.name ?? names[s.id]).padEnd(24), s.size);
  if (!w.linking) { console.log('no linking section'); process.exit(0); }
  const g = buildGraph(w);
  console.log(g.stats, 'nodes', g.nodes.length, 'edges', g.edges.reduce((a, e) => a + e.length, 0));
  const oi = rest.indexOf('--out');
  if (oi >= 0) writeFileSync(rest[oi + 1], JSON.stringify(g));
}
