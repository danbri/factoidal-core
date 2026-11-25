// Explain the corpus. Usage:
//   node src/run.mjs [id ...]        print L1 for the given ids
//   node src/run.mjs --all           write data/out/records.json + coverage
import { corpusPath } from './corpus-path.mjs';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { Names } from './names.mjs';
import { classifyParallax } from './parallax.mjs';
import { explainQuery } from './explain.mjs';
import { renderL1 } from './render.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.join(here, '..');
const corpus = JSON.parse(fs.readFileSync(corpusPath, 'utf8')).queries;
const names = new Names(path.join(root, 'data', 'wikidata-labels.json'));
const comments = JSON.parse(fs.readFileSync(path.join(root, 'data', 'comments.json'), 'utf8')).queries;
// INTERIM: AST from the local Lean dump; replace with factoidal parseSparqlAst.
const asts = {};
for (const line of fs.readFileSync(path.join(root, 'data', 'interim', 'ast-lean-interim.jsonl'), 'utf8').split('\n')) {
  if (!line) continue;
  const r = JSON.parse(line);
  if (r.field === 'lean_replacement_query') asts[r.id] = r.result;
}

/** The parsed Factoidal rewrite (IR), or null. */
export const astOf = (id) => (asts[id]?.ok ? asts[id].ast : null);
/** Readable name for an IRI, from the label cache. */
export const nameOf = (iri) => names.iri(iri);

/** Parallax classification of the parsed rewrite, or null if it didn't parse. */
export function parallaxId(id) {
  const a = asts[id];
  return a?.ok ? classifyParallax(a.ast, (iri) => names.iri(iri)) : null;
}

export function explainId(id) {
  const q = corpus.find(x => x.id === id);
  if (!q) throw new Error(`no query ${id}`);
  const base = { id, title: q.title, status: q.lean_rewrite_status };
  if (!q.lean_replacement_query) {
    const diag = [...q.lean_rewrite_warnings, ...q.lean_rewrite_errors].map(w => w.code || w.message);
    return { stub: true, ...base, reason: q.lean_rewrite_status, diagnostics: diag };
  }
  const a = asts[id];
  if (!a?.ok) return { stub: true, ...base, reason: 'factoidal_parse_failed', diagnostics: [a?.error?.msg] };
  return explainQuery(a.ast, {
    id, title: q.title, names, comments: comments[id] || [], rewrites: q.lean_rewrites,
    status: q.lean_rewrite_status, audit: q.endpoint_audit,
  });
}

const isMain = process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href;
const args = isMain ? process.argv.slice(2) : [];
if (args[0] === '--all') {
  const out = {}, cov = { explained: 0, fully: 0, stub: {}, unexplained: {}, rules: {}, errors: [] };
  for (const q of corpus) {
    let r;
    try { r = explainId(q.id); } catch (e) { cov.errors.push(`${q.id}: ${e.message}`); continue; }
    out[q.id] = r;
    if (r.stub) { cov.stub[r.reason] = (cov.stub[r.reason] || 0) + 1; continue; }
    cov.explained++;
    if (!r.unexplained.length) cov.fully++;
    for (const u of r.unexplained) cov.unexplained[u.what] = (cov.unexplained[u.what] || 0) + 1;
    for (const c of r.caveats) cov.rules[c.rule] = (cov.rules[c.rule] || 0) + 1;
  }
  fs.mkdirSync(path.join(root, 'data', 'out'), { recursive: true });
  fs.writeFileSync(path.join(root, 'data', 'out', 'records.json'), JSON.stringify(out, null, 1) + '\n');
  fs.writeFileSync(path.join(root, 'data', 'out', 'L1.txt'),
    Object.values(out).map(r => r.stub ? `${r.id}\nOriginal title: ${r.title}\n\nSTUB: ${r.reason} ${r.diagnostics.join(', ')}` : renderL1(r)).join('\n\n' + '-'.repeat(72) + '\n\n') + '\n');
  console.log(JSON.stringify(cov, null, 1));
} else {
  for (const id of args) {
    const r = explainId(id);
    console.log(r.stub ? `${id}: STUB ${r.reason} ${r.diagnostics.join(', ')}` : renderL1(r));
    console.log('-'.repeat(72));
  }
}
