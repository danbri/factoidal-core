import assert from 'node:assert/strict';
import { test } from 'node:test';
import { parseSparqlAst } from '../index.mjs';

test('the packaged engine exposes typed SPARQL paths, aggregates and source spans', async () => {
  const text = '# 🍃 path\nSELECT (COUNT(DISTINCT ?item) AS ?n) WHERE { ?item wdt:P31/wdt:P279* wd:Q5 }';
  const { schema_version, ast, source, diagnostics } = await parseSparqlAst(text, { wdqs: true });

  assert.equal(schema_version, 1);
  assert.deepEqual(diagnostics, []);
  assert.equal(source.text, text);
  assert.deepEqual(source.comments, [{ text: '# 🍃 path', start: 0, end: 8 }]);
  assert.equal(ast.form.kind, 'select');
  const [projection] = ast.form.projection;
  assert.equal(projection.variable, 'n');
  assert.equal(projection.expression.fn, 'count');
  assert.equal(projection.expression.distinct, true);
  assert.equal(ast.pattern.kind, 'propertyPath');
  const { path } = ast.pattern;
  assert.equal(path.kind, 'sequence');
  assert.equal(path.left.iri, 'http://www.wikidata.org/prop/direct/P31');
  assert.equal(path.right.kind, 'zeroOrMore');
  const { start, end } = path.source.span;
  assert.equal(Array.from(text).slice(start, end).join(''), 'wdt:P31/wdt:P279*');
});

test('a malformed query keeps source text and points at the error in JavaScript offsets', async () => {
  const text = '# 🍃\nSELECT WHERE {}';
  const { ast, source, diagnostics: [error] } = await parseSparqlAst(text);
  assert.equal(ast, null);
  assert.equal(source.text, text);
  assert.equal(error.code, 'sparql_parse_error');
  assert.equal(text.slice(error.utf16Span.start, error.utf16Span.end), 'WHERE');
  assert.equal(error.utf16Span.start, error.span.start + 1);
});
