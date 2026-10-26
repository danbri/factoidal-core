// Pins every live cell of docs/web/hub/importers.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('importers.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const values = (rows, v) => rows.map((r) => r.get(v) && r.get(v).value);

test('importers: each step produces a Dataset', async () => {
  const csvw = await post.value('fromCsvw');
  assert.equal(csvw.size, 4);
  assert.match(csvw.toString('ntriples'), /<http:\/\/example.org\/station\/pad> <http:\/\/example.org\/opened> "1854"\^\^<http:\/\/www.w3.org\/2001\/XMLSchema#gYear>/);
  const rml = await post.value('fromRml');
  assert.match(rml.toString('ntriples'), /<http:\/\/example.org\/line\/eli> <http:\/\/example.org\/serves> <http:\/\/example.org\/station\/pad>/);
  const jsonld = await post.value('fromJsonLd');
  assert.equal(jsonld.size, 2);
  const xhtml = await post.value('fromXhtml');
  assert.match(xhtml.toString('ntriples'), /"Lift out of service at Paddington"/);
});

test('importers: one named graph per step, joined across steps', async () => {
  const perGraph = await post.value('perGraph');
  assert.deepEqual(values(perGraph, 'g'), ['csvw', 'grddl', 'jsonld', 'rml'].map((s) => `http://example.org/step/${s}`));
  const joined = await post.value('joined');
  assert.deepEqual(values(joined, 'station'), ["King's Cross", 'Paddington']);
  const pad = joined.find((r) => r.get('station').value === 'Paddington');
  assert.equal(pad.get('nameFrom').value, 'http://example.org/step/csvw');
  assert.equal(pad.get('lineFrom').value, 'http://example.org/step/rml');
  assert.equal(pad.get('stepFree').value, 'true');
  assert.match(pad.get('notice').value, /Lift/);
});
