// Pins every live cell in docs/web/hub/25-xml-wellformedness-and-xpath.md.
//
// The post's four cells call `Factoidal.xmlWellformed(xml)` and
// `Factoidal.xpathEval(xml, expr)` -- the raw browser.js exports backed
// by the F*-extracted Parser_XML.parse_xml_document and
// XPath_Eval.eval_xpath_from_root. As in post13/post23, `Factoidal` here
// is a small Node stub that mirrors those browser.js wrappers: it calls
// the SAME npm-entry ABI functions (abi.xmlWellformed / abi.xpathEval)
// the browser build loads, backed by require() instead of fetch().
// `pretty` is the shared node-side stub from _helpers.mjs.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '25-xml-wellformedness-and-xpath.md';

// The cells call the package's typed xmlWellformed -> boolean and
// xpathEval -> XPathResult through `fn`, as the page does (issue 726).
const fn = (await import(NPM_FACTOIDAL_INDEX)).default;
const Factoidal = fn;

const cells = extractObservableCells(POST_FILE);
const B = { Factoidal, fn, pretty };

test('post25: post has 5 live cells (XML hoisted into its own named cell)', () => {
  assert.equal(cells.length, 5, `expected 5 live cells, found ${cells.length}`);
});

test('post25: dependency inference wires XML into cells 2, 4, 5 (not the BAD cell at 3)', () => {
  const post = runReactivePost(cells, B);
  assert.equal(post.names[0], 'XML');
  for (const i of [1, 3, 4]) {
    assert.ok(post.infos[i].refs.includes('XML'), `cell ${i + 1} references XML`);
  }
  assert.ok(!post.infos[2].refs.includes('XML'), 'the BAD cell does not reference XML');
});

test('post25 cell 1 (well-formed document): wellformed true', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[1]);
  assert.deepEqual(result, { wellformed: true });
});

test('post25 cell 2 (mismatched close tag): wellformed false', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[2]);
  assert.deepEqual(result, { wellformed: false });
});

test('post25 cell 3 (//book/title node-set): two title elements', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[3]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['kind', 'name', 'value']);
  assert.deepEqual(result.rows, [
    ['element', 'title', 'SPARQL 1.1'],
    ['element', 'title', 'RDF Primer'],
  ]);
});

test('post25 cell 4 (four XPath result types): number/nodeset/string/boolean', async () => {
  const post = runReactivePost(cells, B);
  const result = await post.value(post.names[4]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['expression', 'resultType', 'value']);
  assert.deepEqual(result.rows, [
    ['count(//book)', 'number', '2'],
    ['//book[1]/title/text()', 'nodeset', 'SPARQL 1.1'],
    ['string(//book[2]/@id)', 'string', 'b2'],
    ['count(//book) > 1', 'boolean', 'true'],
  ]);
});
