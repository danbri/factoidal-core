#!/usr/bin/env node
// check-units.mjs DIR GLUE.mjs [--timing] [--expect corpus.json]: run the corpus through a split engine.
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createEngine } from './unit-loader.mjs';
import { corpus } from './web-render-corpus.mjs';
const [dir, glue, ...rest] = process.argv.slice(2);
const t0 = performance.now();
const factory = (await import(pathToFileURL(resolve(glue)))).default;
const read = u => readFileSync(resolve(dir, u + '.wasm'));
const plan = JSON.parse(readFileSync(resolve(dir, 'units.json'), 'utf8'));
const e = await createEngine({ factory, readUnit: async u => read(u), readUnitSync: rest.includes('--no-sync') ? null : read, units: Object.keys(plan.neededBy) });
const t1 = performance.now();
const m = e.module;
const call0 = (name, types, args) => { const p = m.ccall(name, 'number', types, args); if (!p) return null; try { return m.UTF8ToString(p); } finally { m.ccall('web_render_free', null, ['number'], [p]); } };
// The manifest says which call needs which unit; the loader needs no other knowledge.
const unitsFor = (name, args) => Object.entries(plan.neededBy).filter(([, rules]) => rules.some(r => r.export === name && (!r.op || JSON.parse(args[1]).op === r.op))).map(([u]) => u);
const call = async (name, types, args) => { for (const u of unitsFor(name, args)) await e.ensure(u); return call0(name, types, args); };
const r = call0('web_render_call', ['string', 'number', 'number'], ['<div style="display:grid">x</div>', 120, 160]);
const t2 = performance.now();
if (rest.includes('--timing')) {
  const before = e.isLoaded('xslt');
  await e.ensure('xslt'); const t3 = performance.now();
  const x = call0('web_document_call', ['string', 'string', 'number', 'number'], ['<?xml version="1.0"?><r/>', JSON.stringify({ op: 'xslt', url: 'https://example.test/r.xml', stylesheetURL: 'https://example.test/s.xsl', stylesheet: '<xsl:stylesheet version="3.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:template match="/"><html><body><p>x</p></body></html></xsl:template></xsl:stylesheet>' }), 320, 200]);
  const t4 = performance.now();
  console.log(JSON.stringify({ loadMs: +(t1 - t0).toFixed(1), firstCallMs: +(t2 - t1).toFixed(1), unitLoadMs: +(t3 - t2).toFixed(1), firstXsltMs: +(t4 - t3).toFixed(1), xsltLoadedBefore: before }));
  process.exit(0);
}
const out = await corpus(call);
const i = rest.indexOf('--expect');
if (i >= 0) {
  const want = JSON.parse(readFileSync(rest[i + 1], 'utf8'));
  const bad = Object.keys(want).filter(k => want[k] !== out[k]);
  console.log(JSON.stringify({ cases: Object.keys(want).length, different: bad, loads: e.stats.loads }));
  process.exit(bad.length ? 1 : 0);
}
console.log(JSON.stringify(out));
