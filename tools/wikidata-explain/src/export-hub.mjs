// Export explanations for the Factoidal hub page.
// Usage: node src/export-hub.mjs <out.json>
import { corpusPath } from './corpus-path.mjs';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { explainId, parallaxId } from './run.mjs';
import { renderL1 } from './render.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.join(here, '..');
const out = process.argv[2];
if (!out) { console.error('usage: node src/export-hub.mjs <out.json>'); process.exit(2); }

const corpusDoc = JSON.parse(fs.readFileSync(corpusPath, 'utf8'));
const labels = JSON.parse(fs.readFileSync(path.join(root, 'data', 'wikidata-labels.json'), 'utf8')).meta;

// The explanation body: L1 without the id / title header (the page shows those).
const body = (text) => text.split('\n').slice(1).filter((l, i) => !(i < 3 && /^(Original title:|Query's #title:|$)/.test(l))).join('\n').trim();
const stripTrailer = (q) => (q || '').split('\n# Original query:')[0].trimEnd();

const queries = corpusDoc.queries.map(q => {
  const r = explainId(q.id);
  const base = {
    id: q.id,
    title: q.title,
    section: q.source.section_path,
    source: q.source.revision_url,
    status: q.lean_rewrite_status,
    rewritten: stripTrailer(q.lean_replacement_query) || null,
    original: q.classic_query.trimEnd(),
  };
  if (r.stub) return { ...base, stub: r.reason, diagnostics: r.diagnostics.filter(Boolean) };
  const px = parallaxId(q.id);
  return {
    ...base,
    parallax: px && { tier: px.tier, negations: px.negations.map(n => n.label), blockers: px.blockers },
    titleDirective: r.title_directive && r.title_directive !== q.title ? r.title_directive : undefined,
    explanation: body(renderL1(r)),
    caveats: r.caveats.map(c => ({ rule: c.rule, severity: c.severity })),
    answerChanging: [...new Set(r.caveats.filter(c => c.severity === 'changes_answer').map(c => c.rule))],
  };
});

const doc = {
  schema_version: 1,
  generated: new Date().toISOString().slice(0, 10),
  about: 'Rule-based (deterministic) explanations of the Factoidal rewrites of Martin Poulter\'s Wikidata queries. No language model is used.',
  explained_query: 'lean_replacement_query (the Factoidal rewrite for QLever)',
  parser: 'factoidal Lean parser L4Factoidal.Wikidata.parseQuerySyntax via an interim JSON export; to be replaced by parseSparqlAst',
  labels: { retrieved: labels.retrieved, source: labels.source, license: labels.license },
  corpus: {
    license: corpusDoc.license, license_url: corpusDoc.license_url, attribution: corpusDoc.attribution,
    corpus_sha256: corpusDoc.corpus_sha256, lean_git_commit: corpusDoc.lean_git_commit,
  },
  counts: {
    total: queries.length,
    explained: queries.filter(q => !q.stub).length,
    stubs: queries.filter(q => q.stub).reduce((a, q) => ((a[q.stub] = (a[q.stub] || 0) + 1), a), {}),
  },
  parallax: {
    tiers: queries.reduce((a, q) => (q.parallax && (a[q.parallax.tier] = (a[q.parallax.tier] || 0) + 1), a), {}),
    withNegation: queries.filter(q => q.parallax?.negations.length && q.parallax.tier !== 'N').length,
    byTier: ['A', 'B', 'C', 'D'].map(tier => ({ tier, ids: queries.filter(q => q.parallax?.tier === tier).map(q => q.id) })),
    byBlocker: Object.entries(queries.reduce((acc, q) => {
      for (const b of q.parallax?.blockers || []) (acc[b] ||= []).push(q.id);
      return acc;
    }, {})).sort((x, y) => y[1].length - x[1].length).map(([blocker, ids]) => ({ blocker, ids })),
  },
  // Static index for the page: answer-changing rule -> query ids.
  byRule: Object.entries(queries.reduce((acc, q) => {
    for (const rule of q.answerChanging || []) (acc[rule] ||= []).push(q.id);
    return acc;
  }, {})).sort((x, y) => y[1].length - x[1].length).map(([rule, ids]) => ({ rule, ids })),
  queries,
};
fs.writeFileSync(out, JSON.stringify(doc) + '\n');
console.log(`wrote ${out}: ${doc.counts.explained} explained, stubs ${JSON.stringify(doc.counts.stubs)}, ${(fs.statSync(out).size / 1e6).toFixed(2)} MB`);
