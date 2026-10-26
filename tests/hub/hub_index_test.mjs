// Pins the live cell of docs/web/hub/index.md and the build-time data
// file of its standards table (docs/_data/hubStandards.js).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

import { extractObservableCells, runReactivePost, pretty, HUB_PAGE_DIR } from './_helpers.mjs';
import * as Factoidal from '../../npm/factoidal/index.mjs';

const require = createRequire(import.meta.url);

test('hub index: the API cell', async () => {
  const post = runReactivePost(extractObservableCells('index.md', HUB_PAGE_DIR), { Factoidal, fn: Factoidal.default, pretty });
  assert.equal(await post.value('example'), 'hello');
});

test('hub index: the standards table comes from a scoreboard record', () => {
  const data = require('../../docs/_data/hubStandards.js')();
  assert.match(data.file, /^lean-scoreboard-\d{4}-\d{2}-\d{2}\.json$/);
  assert.ok(data.rows.length >= 20, `${data.rows.length} rows`);
  for (const row of data.rows) {
    assert.ok(row.area && row.suite && row.text, JSON.stringify(row));
    if (row.measured && /pass/.test(row.text)) assert.match(row.text, /^\d+ pass, \d+ fail(, \d+ other)? \(out of \d+\)$/);
  }
  const sparql = data.rows.find((r) => /^SPARQL 1\.1 \(query/.test(r.area));
  assert.ok(sparql, 'a SPARQL 1.1 row');
});
