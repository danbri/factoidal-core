// Pins docs/web/hub/sparql-rl.md.
//
// 1. Every theorem the page names in a table row
//    | `name` | `formal/lean4/...lean` | ... |
//    is declared (`theorem name`) in that file.
// 2. Every stated output (a ```text block after
//    <!-- expect CELL DATA_CELL RULES_CELL -->) equals what the engine
//    produces for the cell CELL, compared as sorted lines with blank nodes
//    written `[]`. The engine is the npm API (npm/factoidal/index.mjs with
//    the wasm in npm/factoidal/l4-assets/, $FACTOIDAL_L4_ASSETS or
//    docs/web/hub/assets/l4/). When that does not load, the native
//    formal/lean4/.lake/build/bin/l4wasm-cli (or $FACTOIDAL_L4WASM_CLI)
//    runs the op datasetSparqlRlInfer on the DATA_CELL and RULES_CELL
//    strings. When neither is there, the engine checks skip with a message.
// 3. With the npm API: the RIF comparison, the OWL 2 RL check and the
//    rejections cell.

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const REPO = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const PAGE = 'sparql-rl.md';
const text = fs.readFileSync(path.join(HUB_PAGE_DIR, PAGE), 'utf8');

// ---------------------------------------------------------------------
// Theorems

const theoremRows = [...text.matchAll(/^\| `([A-Za-z0-9_.']+)` \| `(formal\/lean4\/[^`]+\.lean)` \|/gm)]
  .map((m) => ({ name: m[1], file: m[2] }));

test('sparql-rl: the page names theorems', () => {
  assert.ok(theoremRows.length >= 10, `found ${theoremRows.length} theorem rows`);
});

for (const { name, file } of theoremRows) {
  test(`sparql-rl: theorem ${name} is declared in ${file}`, () => {
    const src = fs.readFileSync(path.join(REPO, file), 'utf8');
    const re = new RegExp(`^theorem\\s+${name.replace(/[.]/g, '\\.')}(\\s|$)`, 'm');
    assert.match(src, re, `no 'theorem ${name}' in ${file}`);
  });
}

// ---------------------------------------------------------------------
// Stated outputs

const expectations = [...text.matchAll(/<!-- expect (\S+) (\S+) (\S+) -->\n```text\n([\s\S]*?)```/g)]
  .map((m) => ({ cell: m[1], dataCell: m[2], rulesCell: m[3], lines: m[4].split('\n').filter(Boolean).sort() }));

test('sparql-rl: the page states outputs', () => {
  assert.ok(expectations.length >= 6, `found ${expectations.length} stated outputs`);
});

const EX = 'http://example/';
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

// The page's notation for one term of an RDF/JS quad.
function termText(t) {
  switch (t.termType) {
    case 'NamedNode':
      if (t.value.startsWith(EX)) return ':' + t.value.slice(EX.length);
      if (t.value.startsWith(RDF)) return 'rdf:' + t.value.slice(RDF.length);
      return `<${t.value}>`;
    case 'BlankNode': return '[]';
    case 'Quad': return `<<( ${termText(t.subject)} ${termText(t.predicate)} ${termText(t.object)} )>>`;
    case 'Literal': {
      const dt = t.datatype && t.datatype.value;
      if (t.language) return `${JSON.stringify(t.value)}@${t.language}`;
      if (dt === XSD + 'integer' || dt === XSD + 'decimal' || dt === XSD + 'boolean') return t.value;
      if (!dt || dt === XSD + 'string') return JSON.stringify(t.value);
      return `${JSON.stringify(t.value)}^^<${dt}>`;
    }
    default: return String(t.value);
  }
}
const lineOf = (q) => `${termText(q.subject)} ${termText(q.predicate)} ${termText(q.object)} .`;

// A small N-Quads 1.2 term reader, for the native path's output.
function parseNQuadsLine(line) {
  let i = 0;
  const ws = () => { while (line[i] === ' ' || line[i] === '\t') i++; };
  const term = () => {
    ws();
    if (line.startsWith('<<(', i)) {
      i += 3;
      const s = term(), p = term(), o = term();
      ws();
      if (!line.startsWith(')>>', i)) throw new Error(`bad triple term: ${line}`);
      i += 3;
      return { termType: 'Quad', subject: s, predicate: p, object: o };
    }
    if (line[i] === '<') { const j = line.indexOf('>', i); const v = line.slice(i + 1, j); i = j + 1; return { termType: 'NamedNode', value: v }; }
    if (line.startsWith('_:', i)) { const m = /^_:[^\s]+/.exec(line.slice(i)); i += m[0].length; return { termType: 'BlankNode', value: m[0].slice(2) }; }
    if (line[i] === '"') {
      let j = i + 1, v = '';
      while (line[j] !== '"') { if (line[j] === '\\') { v += JSON.parse(`"${line.slice(j, j + 2)}"`); j += 2; } else v += line[j++]; }
      i = j + 1;
      if (line.startsWith('^^<', i)) { const k = line.indexOf('>', i); const dt = line.slice(i + 3, k); i = k + 1; return { termType: 'Literal', value: v, datatype: { value: dt } }; }
      if (line[i] === '@') { const m = /^@[A-Za-z0-9-]+/.exec(line.slice(i)); i += m[0].length; return { termType: 'Literal', value: v, language: m[0].slice(1) }; }
      return { termType: 'Literal', value: v, datatype: { value: XSD + 'string' } };
    }
    throw new Error(`cannot read N-Quads term at ${i}: ${line}`);
  };
  const s = term(), p = term(), o = term();
  return { subject: s, predicate: p, object: o };
}

// ---------------------------------------------------------------------
// The engines

let npmReason = null;
try {
  const caps = await Factoidal.capabilities();
  if (!caps.sparqlRl) npmReason = 'the loaded engine has no sparqlRl op';
} catch (e) {
  npmReason = `the npm engine did not load (${e.message.split('\n')[0]})`;
}
const npmOk = npmReason === null;

const cliPath = process.env.FACTOIDAL_L4WASM_CLI || path.join(REPO, 'formal', 'lean4', '.lake', 'build', 'bin', 'l4wasm-cli');
const cliOk = !npmOk && fs.existsSync(cliPath);

function nativeInfer(data, rules) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'hub-srl-'));
  try {
    const seq = path.join(dir, 'seq.json');
    fs.writeFileSync(seq, JSON.stringify([
      ['datasetOpen', [data, 'turtle', '']],
      ['datasetSparqlRlInfer', ['h1', rules]],
      ['datasetSerialize', ['h2', 'nquads']],
    ]));
    const out = execFileSync(cliPath, ['callseq', seq], { encoding: 'utf8', maxBuffer: 1 << 26 });
    const rs = out.split('\n').filter((l) => l.trim()).map((l) => JSON.parse(l));
    if (!rs[1] || rs[1].ok !== true) throw new Error(`datasetSparqlRlInfer failed: ${JSON.stringify(rs[1])}`);
    return rs[2].nquads.split('\n').filter((l) => l.trim()).map(parseNQuadsLine);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

const skipReason = npmOk || cliOk ? false
  : `${npmReason}; no native l4wasm-cli at ${cliPath}. Set FACTOIDAL_L4_ASSETS to the l4-assets/ of @factoidal/core, or build l4wasm-cli`;
if (skipReason) console.log(`# hub_sparql-rl: engine checks skipped: ${skipReason}`);
else console.log(`# hub_sparql-rl: engine = ${npmOk ? 'npm API' : `native ${cliPath}`}`);

const cells = extractObservableCells(PAGE, HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

for (const ex of expectations) {
  test(`sparql-rl: stated output of ${ex.cell}`, { skip: skipReason }, async () => {
    let quads;
    if (npmOk) {
      quads = [...await post.value(ex.cell)];
    } else {
      // The data and rules cells are plain strings: the runtime evaluates
      // them without the engine.
      quads = nativeInfer(await post.value(ex.dataCell), await post.value(ex.rulesCell));
    }
    assert.deepEqual(quads.map(lineOf).sort(), ex.lines);
  });
}

const npmOnly = npmOk ? false : (skipReason || 'needs the npm API (RIF and OWL closure are not driven through the native path here)');

test('sparql-rl: the stated rejection messages', { skip: npmOnly }, async () => {
  const rows = await post.value('rejections');
  const stated = [...text.matchAll(/^\| (syntax error|not well-formed|not stratifiable) \| `([^`]+)` \|$/gm)]
    .map((m) => ({ ruleSet: m[1], result: m[2] }));
  assert.equal(stated.length, 3);
  assert.deepEqual(rows, stated);
});

test('sparql-rl: RIF Core and SPARQL-RL derive the same :exposedTo triples', { skip: npmOnly }, async () => {
  const r = await post.value('rifVsSrl');
  assert.equal(r.same, true);
  assert.deepEqual(r.rif, ['http://example/app http://example/vuln1', 'http://example/db http://example/vuln1', 'http://example/frontend http://example/vuln1']);
  assert.equal(r.inputSize, 9);
  assert.equal(r.rifSize, 12);
  assert.equal(r.sparqlRlSize, 3);
});

test('sparql-rl: every triple of the five OWL 2 RL rules is in closure(owl-rl)', { skip: npmOnly }, async () => {
  const r = await post.value('owlCheck');
  assert.equal(r.derived, 8);
  assert.equal(r.alsoInClosure, 8);
});

test('sparql-rl: the OWL 2 RL rules on the page are copied from OwlRl.lean', () => {
  const lean = fs.readFileSync(path.join(REPO, 'formal/lean4/L4Factoidal/SPARQLRL/OwlRl.lean'), 'utf8');
  const m = /owlRules = `([\s\S]*?)`/.exec(text);
  assert.ok(m, 'owlRules cell');
  const rules = m[1].split(/\n(?=# )/).filter((b) => b.startsWith('# '));
  assert.equal(rules.length, 5);
  for (const block of rules) assert.ok(lean.includes(block.trim()), `not in OwlRl.lean:\n${block}`);
});
