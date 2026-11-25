import { corpusPath } from './corpus-path.mjs';
import fs from 'node:fs';
import { classifyParallax } from './parallax.mjs';
import { Names } from './names.mjs';
const names = new Names('data/wikidata-labels.json');
const nm = (iri) => names.iri(iri);
const asts = {};
for (const line of fs.readFileSync('data/interim/ast-lean-interim.jsonl', 'utf8').split('\n')) {
  if (!line) continue; const r = JSON.parse(line);
  if (r.field === 'lean_replacement_query') asts[r.id] = r.result;
}
const corpus = JSON.parse(fs.readFileSync(corpusPath, 'utf8')).queries;
const tiersNeg = {}, negCount = {};
const out = {}, tiers = {}, blockers = {}, soleBlocker = {};
for (const q of corpus) {
  const a = asts[q.id];
  if (!a?.ok) { out[q.id] = { tier: 'unparsed' }; tiers.unparsed = (tiers.unparsed || 0) + 1; continue; }
  const r = classifyParallax(a.ast, nm);
  const key = r.tier === 'N' ? 'N' : r.negations.length ? r.tier + '+neg' : r.tier;
  tiersNeg[key] = (tiersNeg[key] || 0) + 1;
  if (r.negations.length) negCount[r.negations.length] = (negCount[r.negations.length] || 0) + 1;
  out[q.id] = r; tiers[r.tier] = (tiers[r.tier] || 0) + 1;
  for (const b of r.blockers) blockers[b] = (blockers[b] || 0) + 1;
  if (r.blockers.length === 1) soleBlocker[r.blockers[0]] = (soleBlocker[r.blockers[0]] || 0) + 1;
}
fs.writeFileSync('data/out/parallax.json', JSON.stringify(out, null, 1));
console.log(JSON.stringify({ tiers, tiersNeg, negCount, blockers, soleBlocker }, null, 1));
