#!/usr/bin/env node
// Exercise the public JS/Wasm parser against the complete prepared corpus.
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { parseSparqlAst, wikidataRewrite } from '../../npm/factoidal/index.mjs';

const [file] = process.argv.slice(2);
if (!file) throw new Error('Usage: node tools/wikidata/audit_query_ast.mjs MLP-CATALOGUE.json');
const { queries } = JSON.parse(await readFile(file, 'utf8'));

function* walk(node) {
  if (Array.isArray(node)) {
    for (const child of node) yield* walk(child);
  } else if (node && typeof node === 'object') {
    if (typeof node.kind === 'string') yield node;
    for (const child of Object.values(node)) yield* walk(child);
  }
}

function checkSource(doc, text) {
  assert.equal(doc.schema_version, 1);
  assert.match(doc.parser_version, /factoidal-sparql-/);
  assert.equal(doc.source.text, text);
  assert.equal(doc.source.offsetEncoding, 'unicode-code-points');
  assert.equal(Boolean(doc.ast), doc.diagnostics.length === 0);
  if (!doc.ast) assert.ok(doc.diagnostics.every(diagnostic => diagnostic.code && diagnostic.message));
  const chars = Array.from(text);
  for (const item of [...doc.source.tokens, ...doc.source.comments]) {
    const { start, end } = item.span ?? item;
    assert.equal(chars.slice(start, end).join(''), item.text);
  }
  const checkSpan = ({ start, end }) => {
    assert.ok(Number.isInteger(start) && Number.isInteger(end));
    assert.ok(0 <= start && start < end && end <= chars.length);
  };
  for (const anchor of doc.source.anchors) checkSpan(anchor.span);
  for (const ast of [doc.ast, ...doc.namedSubqueries.map(definition => definition.ast)]) {
    for (const node of walk(ast)) {
      assert.ok(node.source, `missing source on ${node.kind}`);
      const { origin, span, spans, reason } = node.source;
      assert.ok(Object.hasOwn(origins, origin), `unknown source origin ${origin}`);
      origins[origin]++;
      if (origin === 'exact') {
        checkSpan(span);
        assert.equal(spans, undefined);
      } else {
        assert.equal(typeof reason, 'string');
        assert.ok(reason.length > 0);
        assert.equal(span, undefined);
        if (origin === 'derived') {
          assert.ok(Array.isArray(spans) && spans.length > 0);
          spans.forEach(checkSpan);
        } else {
          assert.equal(spans, undefined);
          if (origin === 'unmapped') unmappedReasons[reason] = (unmappedReasons[reason] ?? 0) + 1;
        }
      }
    }
  }
}

const checks = {
  'mlp-003': [['propertyPath', 'sequence', 'zeroOrMore', 'aggregate'], ['wdt:P31', 'wdt:P279', 'wd:Q13442814']],
  'mlp-349': [['minus', 'bnode', 'aggregate'], ['wdt:P217', 'wdt:P195']],
  'mlp-268': [['minus', 'aggregate'], ['p:P195', 'ps:P195', 'pq:P582']],
  'mlp-030': [['union', 'sequence', 'aggregate'], ['wdt:P69', 'wdt:P31']],
  'mlp-352': [['values', 'literal', 'lang'], ['rdfs:label', 'skos:altLabel']],
  'mlp-382': [['leftJoin'], ['wdt:P1433', 'schema:about', 'schema:isPartOf']],
  'mlp-348': [['bind', 'filter', 'notExistsPat', 'sequence'], ['wdt:P1476', 'rdfs:label']],
  'mlp-248': [['minus', 'aggregate'], ['wdt:P276', 'wdt:P625']],
  'mlp-345': [['subSelect', 'aggregate', 'desc'], ['wdt:P6698', 'wdt:P218']],
  'mlp-117': [['aggregate', 'compare', 'desc'], ['wikibase:badge', 'schema:about']],
  'mlp-197': [['leftJoin', 'minus', 'year'], ['wdt:P31', 'wdt:P18', 'wdt:P569']],
  'mlp-329': [['service'], ['wikibase:mwapi']],
  'mlp-039': [['leftJoin', 'minus', 'aggregate'], ['wdt:P131', 'wdt:P576', 'pq:P625']],
};

function checkTargets(row, original, replacement) {
  const doc = replacement ?? original;
  assert.ok(doc.ast, JSON.stringify([row.id, doc.diagnostics]));
  const nodes = [...walk(doc.ast)];
  const [kinds, names] = checks[row.id];
  for (const kind of kinds) assert.ok(nodes.some(node => node.kind === kind), `${row.id} ${kind}`);
  for (const name of names) {
    assert.ok(doc.source.tokens.some(token => token.text === name && token.iri), `${row.id} ${name}`);
  }
  if (row.id === 'mlp-349') {
    const idSet = new Set(doc.source.blankNodes.filter(node => node.kind === 'anonymous').map(node => node.id));
    assert.equal(idSet.size, 2);
    assert.ok(nodes.filter(node => node.kind === 'bnode').every(node => idSet.has(node.id)));
  }
  if (row.id === 'mlp-352') {
    assert.ok(nodes.filter(node => node.kind === 'values').every(node => node.rows.length === 2));
    assert.ok(nodes.some(node => node.kind === 'literal' && node.value === 'Confucius' && node.language === 'en'));
    assert.equal(doc.ast.modifier.distinct, true);
  }
  if (row.id === 'mlp-382') {
    const note = original.source.comments.find(comment => /published in/i.test(comment.text));
    assert.ok(note);
    const chars = Array.from(original.source.text);
    assert.ok(original.source.anchors.some(anchor => anchor.kind === 'triple' &&
      chars.slice(anchor.span.start, anchor.span.end).join('').includes('wdt:P1433') &&
      /^[. \t]*$/.test(chars.slice(anchor.span.end, note.start).join(''))));
  }
  if (row.id === 'mlp-248') assert.ok(nodes.some(node => node.kind === 'aggregate' && node.fn === 'sample'));
  if (row.id === 'mlp-117') assert.ok(doc.ast.having.length && doc.ast.groupBy.length);
  if (row.id === 'mlp-329') assert.equal(row.lean_rewrite_status, 'skipped_unsupported');
  if (row.id === 'mlp-039') assert.ok(doc.source.directives.some(d => d.kind === 'defaultView' && d.value.startsWith('Map')));
}

let originalsParsed = 0;
const origins = { exact: 0, derived: 0, synthetic: 0, unmapped: 0 };
const unmappedReasons = {};
let replacementsParsed = 0;
let replacements = 0;
let namedReplacements = 0;
let targets = 0;
const originalDiagnostics = [];
const replacementDiagnostics = [];
for (const row of queries) {
  const original = await parseSparqlAst(row.classic_query, { wdqs: true });
  checkSource(original, row.classic_query);
  if (original.ast) originalsParsed += 1;
  else originalDiagnostics.push({ id: row.id, code: original.diagnostics[0].code });
  let replacement;
  if (typeof row.lean_replacement_query === 'string') {
    replacements += 1;
    replacement = await parseSparqlAst(row.lean_replacement_query, { wdqs: true });
    checkSource(replacement, row.lean_replacement_query);
    if (replacement.ast) replacementsParsed += 1;
    else replacementDiagnostics.push({ id: row.id, code: replacement.diagnostics[0].code });
    if (replacement.namedSubqueries.length) namedReplacements += 1;
  }
  if (row.id in checks) {
    checkTargets(row, original, replacement);
    targets += 1;
  }
}

const aggregates = await parseSparqlAst(
  'SELECT (COUNT(*) AS ?a) (COUNT(DISTINCT *) AS ?b) (COUNT(true) AS ?c) (COUNT(DISTINCT ?x) AS ?d) ' +
  '(GROUP_CONCAT(?x; SEPARATOR=" / ") AS ?e) WHERE { VALUES ?x { 1 2 UNDEF } } ORDER BY DESC(?a) LIMIT 5'
);
assert.ok(aggregates.ast, JSON.stringify(aggregates.diagnostics));
const [count, distinct, expression, values, concat] = aggregates.ast.form.projection.map(item => item.expression);
assert.deepEqual([count.arg.kind, distinct.arg.kind, expression.arg.kind, values.arg.kind],
  ['wildcard', 'wildcard', 'literal', 'var']);
assert.deepEqual([count.distinct, distinct.distinct, expression.distinct, values.distinct],
  [false, true, false, true]);
assert.equal(concat.separator, ' / ');
assert.equal(aggregates.ast.pattern.rows[2][0], null);

const invalid = await parseSparqlAst('# 🗺\nASK {} }');
assert.equal(invalid.ast, null);
assert.deepEqual(invalid.diagnostics[0].span, { start: 11, end: 12 });
assert.deepEqual(invalid.diagnostics[0].utf16Span, { start: 12, end: 13 });

const abbreviated = await parseSparqlAst('ASK { ?s <urn:p> ?a, ?b ; <urn:q> ?c }');
assert.deepEqual(abbreviated.source.anchors.map(item =>
  [item.origin, abbreviated.source.text.slice(item.span.start, item.span.end)]),
[['exact', '?s <urn:p> ?a'], ['derived', '?b'], ['derived', '<urn:q> ?c']]);
assert.ok(abbreviated.source.anchors.every(item => item.subject.start === 6));

const preserveInput = '#title: 🗺 test\nSELECT ?x ?xLabel WHERE { ?x wdt:P31 wd:Q5 . # inline\n' +
  'SERVICE wikibase:label { bd:serviceParam wikibase:language "en" . # relocated\n} }';
const ordinary = await wikidataRewrite(preserveInput);
const preserved = await wikidataRewrite(preserveInput, { preserveComments: true });
assert.equal(ordinary.rewrite_status, 'rewritten');
assert.equal(preserved.rewrite_status, 'rewritten');
const body = preserved.rewritten_query.split('\n# Original query:')[0];
assert.ok(body.includes('wd:Q5 . # inline'));
assert.ok(body.includes('\n# relocated\n'));
assert.ok((await parseSparqlAst(body)).ast);

assert.equal(targets, Object.keys(checks).length);
console.log(JSON.stringify({ queries: queries.length, originalsParsed, replacementsParsed,
  replacements, namedReplacements, targets, originalDiagnostics, replacementDiagnostics,
  origins, unmappedReasons }, null, 2));
if (replacementDiagnostics.length) process.exitCode = 1;
