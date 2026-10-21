// Pins every live cell of docs/web/hub/validation.md (see
// hub_rdf_syntaxes_test.mjs for the harness shape).

import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const cells = extractObservableCells('validation.md', HUB_PAGE_DIR);
const post = runReactivePost(cells, { Factoidal, fn: Factoidal.default, pretty });
const tail = (t) => t.value.split(/[/#]/).pop();

test('validation: SHACL report as a Dataset', async () => {
  assert.equal(await post.value('conforms'), false);
  assert.ok((await post.value('report')).size > 0);
  const rows = await post.value('violations');
  const got = rows.map((r) => `${tail(r.get('focus'))} ${tail(r.get('component'))}`).sort();
  assert.deepEqual(got, ['bob ClassConstraintComponent', 'bob DatatypeConstraintComponent', 'bob MinCountConstraintComponent']);
});

test('validation: SHACL-SPARQL constraint', async () => {
  assert.equal(await post.value('sparqlConstraint'), false, 'alice knows bob who knows carol, a Document');
});

test('validation: ShEx', async () => {
  assert.deepEqual(await post.value('shexResults'), { alice: false, bob: false, carol: false });
});
