// Pins every live cell of docs/web/hub/canonical-and-credentials.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';

import { extractObservableCells, runReactivePost, pretty, xfail, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('canonical-and-credentials.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });

test('canonical: isomorphic documents, one canonical form, its SHA-256', async () => {
  const canonical = await post.value('canonical');
  assert.match(canonical, /_:c14n0/);
  assert.equal(await post.value('sameGraph'), true);
  assert.equal(await post.value('digest'), createHash('sha256').update(canonical).digest('hex'));
  assert.equal(await post.value('hash'), await post.value('digest'));
  assert.match(await post.value('hash'), /^[0-9a-f]{64}$/);
});

test('canonical: eddsa-rdfc-2022 sign, verify, tamper', async () => {
  assert.equal(await post.value('publicKey'), 'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a');
  assert.match(await post.value('proofValue'), /^z[1-9A-HJ-NP-Za-km-z]+$/);
  assert.equal(await post.value('verified'), true);
  assert.equal(await post.value('afterTamper'), false);
});

test('canonical: did:key resolves to a DID document', async () => {
  const doc = await post.value('didDocument');
  assert.ok(doc.size > 0);
  assert.match(doc.toString('ntriples'), /did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK/);
});

xfail('canonical: RDFC-1.0 of a dataset with an RDF 1.2 triple term', 'https://github.com/danbri/factoidal/issues/873', async () => {
  const ds = await Factoidal.parse('VERSION "1.2"\n@prefix ex: <http://example.org/> .\nex:a ex:said <<( ex:b ex:p ex:c )>> .', { format: 'turtle12' });
  assert.match(await ds.canonicalize(), /<<\(/);
});
