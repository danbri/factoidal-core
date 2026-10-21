// Pins every live cell of docs/web/hub/rdf-syntaxes.md. The cells run
// through the same reactive runtime the page uses, with `Factoidal` bound
// to the npm package's Node entry (the browser entry exports the same
// names; tests/hub/fn_surface_parity_test.mjs checks that).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('rdf-syntaxes.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

test('rdf-syntaxes: Turtle read, six writers, round trips', async () => {
  const summary = await post.value('summary');
  assert.equal(summary.quads, 5);
  assert.equal(summary.prefixes.foaf, 'http://xmlns.com/foaf/0.1/');
  const written = await post.value('written');
  assert.match(written.ntriples, /<http:\/\/example.org\/alice> <http:\/\/xmlns.com\/foaf\/0.1\/name> "Alice" \./);
  assert.match(written.rdfxml, /rdf:RDF/);
  assert.equal(await post.value('sameAfterRdfXml'), true);
  assert.equal(await post.value('sameAfterJsonLd'), true);
});

test('rdf-syntaxes: strict error position and lenient diagnostics', async () => {
  const err = await post.value('syntaxError');
  assert.equal(err.name, 'FactoidalError');
  assert.equal(err.code, 'parse.syntax');
  assert.equal(err.line, 2);
  const lenient = await post.value('lenient');
  assert.equal(lenient.quads, 2);
  assert.equal(lenient.diagnostics.length, 1);
  assert.match(lenient.diagnostics[0], /^2:/);
});

test('rdf-syntaxes: RDF 1.2 Turtle', async () => {
  const ds12 = await post.value('ds12');
  assert.ok(ds12.size >= 5, `RDF 1.2 dataset has ${ds12.size} quads`);
  const nq = await ds12.serialize({ format: 'nquads' });
  assert.match(nq, /<<\( <http:\/\/example.org\/bob> <http:\/\/example.org\/likes> <http:\/\/example.org\/tea> \)>>/);
  assert.match(nq, /"hello"@en--ltr/);
  assert.notEqual(await post.value('refusedAs11'), 'accepted');
});

xfail('rdf-syntaxes: RDF/XML writes an RDF 1.2 triple term', 'https://github.com/danbri/factoidal/issues/883', async () => {
  const ds12 = await post.value('ds12');
  const xml = await ds12.serialize({ format: 'rdfxml', version: '1.2' });
  const back = await Factoidal.parse(xml, { format: 'rdfxml' });
  assert.equal(back.size, ds12.size);
});
