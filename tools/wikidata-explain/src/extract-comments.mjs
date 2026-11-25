// Run the comment extractor over the corpus.
// Usage: node src/extract-comments.mjs ../mlp-all-queries.json data/comments.json
import fs from 'node:fs';
import { extractComments } from './comments.mjs';

const [, , input, output] = process.argv;
if (!input || !output) {
  console.error('usage: node src/extract-comments.mjs <mlp-all-queries.json> <out.json>');
  process.exit(2);
}
const corpus = JSON.parse(fs.readFileSync(input, 'utf8'));
const out = {
  meta: {
    source: 'classic_query',
    why_classic: 'Comments are taken from the original (after input preparation). The Factoidal rewrite drops most of them on re-serialisation, so attaching a comment to the explained query needs rewrite provenance (PARSE-API-NEEDS item 10).',
    offsets: 'UTF-16 code-unit indices into classic_query; line/column 1-based',
    generated: new Date().toISOString().slice(0, 10),
  },
  queries: {},
};
const stats = { queries: 0, withComments: 0, comments: 0, directives: {}, views: {}, viewErrors: [] };
for (const q of corpus.queries) {
  const cs = extractComments(q.classic_query);
  stats.queries++;
  if (cs.some(c => c.kind === 'comment')) stats.withComments++;
  for (const c of cs) {
    if (c.kind === 'comment') stats.comments++;
    else {
      stats.directives[c.name] = (stats.directives[c.name] || 0) + 1;
      if (c.name === 'defaultView') {
        const v = c.parsed?.view ?? '(unparsed)';
        stats.views[v] = (stats.views[v] || 0) + 1;
        if (c.parsed?.error) stats.viewErrors.push(`${q.id}: ${c.parsed.error}: ${c.value}`);
      }
    }
  }
  if (cs.length) out.queries[q.id] = cs;
}
fs.writeFileSync(output, JSON.stringify(out, null, 1) + '\n');
console.log(JSON.stringify(stats, null, 1));
