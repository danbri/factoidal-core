// Export the set-browsing (Parallax) view for its own Factoidal hub page.
// Usage: node src/export-parallax-hub.mjs <out.json>
import { corpusPath } from './corpus-path.mjs';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { astOf, nameOf, parallaxId } from './run.mjs';
import { buildFlow } from './flow.mjs';
import { blocksOf } from './blocks.mjs';
import { plainReason } from './plain.mjs';

const root = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const out = process.argv[2];
if (!out) { console.error('usage: node src/export-parallax-hub.mjs <out.json>'); process.exit(2); }
const corpusDoc = JSON.parse(fs.readFileSync(corpusPath, 'utf8'));
const labels = JSON.parse(fs.readFileSync(path.join(root, 'data', 'wikidata-labels.json'), 'utf8'));
const images = JSON.parse(fs.readFileSync(path.join(root, 'data', 'wikidata-images.json'), 'utf8'));

const TIER = {
  A: 'Core set browsing',
  B: 'With value filters or computed columns',
  C: 'Through statements and qualifiers',
  D: 'Using subclasses to choose the type',
  N: 'Beyond set browsing',
};
/** How a card names the starting set: its type, else its first facet, else its variable. */
const bare = (t) => t.replace(/ \((Q|P)\d+\)/g, '').replace(/ \[redirect → Q\d+\]/g, '');
function startOf(set) {
  if (!set) return { start: null, startId: null };
  if (set.typeId) return { start: set.title, startId: set.typeId };
  const f = set.facets.find(x => !x.optional && x.values.length);
  if (f) return { start: `items with ${bare(f.prop)} = ${f.values.map(v => bare(v.text)).join(' or ')}`, startId: f.values.find(v => v.id)?.id ?? null };
  return { start: `?${set.var}`, startId: null };
}
function plainOps(prog) {
  for (const it of prog.items) if (it.op) { if (it.op.why) it.op.whyText = plainReason(it.op.why); it.op.slots.forEach(plainOps); }
}
function collectBlockEntities(prog, ids) {
  for (const it of prog.items) {
    if (it.chain) for (const row of it.chain.rows) for (const p of row) {
      if (p.typeId) ids.add(p.typeId);
      for (const f of p.facets || []) for (const v of f.values) if (v.id) ids.add(v.id);
    } else for (const s of it.op.slots) collectBlockEntities(s, ids);
  }
}
const queries = [], entityIds = new Set();
for (const q of corpusDoc.queries) {
  const ast = astOf(q.id);
  if (!ast) continue;
  const px = parallaxId(q.id);
  const flow = buildFlow(ast, px, nameOf);
  flow.entities.forEach(e => entityIds.add(e));
  // The query as blocks: chains of interlocking pieces, held by operator blocks.
  const blocks = blocksOf(ast, nameOf);
  collectBlockEntities(blocks, entityIds);
  plainOps(blocks);
  flow.why = flow.beyond.map(b => ({ code: b, text: plainReason(b) }));
  // The page draws blocks; the set list itself is not needed there.
  const { sets: flowSets, looseEdges, ...flowOut } = flow;
  const kinds = [...new Set([...(px.negations.length ? ['exclude'] : []), ...px.extensions.map(e => e.kind)])];
  queries.push({
    id: q.id, title: q.title, tier: px.tier, tierName: TIER[px.tier], kinds,
    ...startOf(flowSets[0]),
    sets: flowSets.length, flow: flowOut, blocks,
    wdqs: `https://query.wikidata.org/#${encodeURIComponent(q.classic_query)}`,
  });
}
const entities = {};
for (const id of entityIds) {
  const e = labels.entities[id] || {};
  entities[id] = { label: e.label || id, description: e.description || '', image: images.images[id] || null };
}
const tiers = ['A', 'B', 'C', 'D', 'N'].map(t => ({ tier: t, name: TIER[t], ids: queries.filter(q => q.tier === t).map(q => q.id) }));
const doc = {
  generated: new Date().toISOString().slice(0, 10),
  counts: { total: corpusDoc.queries.length, classified: queries.length,
    withExclusions: queries.filter(q => q.kinds.includes('exclude') && q.tier !== 'N').length,
    withExtensions: queries.filter(q => q.kinds.some(k => k !== 'exclude') && q.tier !== 'N').length },
  tiers, queries, entities,
  thumb: 'https://commons.wikimedia.org/wiki/Special:FilePath/',
  sources: { labels: labels.meta.retrieved, images: images.meta },
  corpus: { license: corpusDoc.license, license_url: corpusDoc.license_url, attribution: corpusDoc.attribution },
};
fs.writeFileSync(out, JSON.stringify(doc) + '\n');
console.log(`wrote ${out}: ${queries.length} queries, ${Object.keys(entities).length} entities (${Object.values(entities).filter(e => e.image).length} with images), ${(fs.statSync(out).size / 1e6).toFixed(2)} MB`);
