// @factoidal/core/sample-store packs a small store from inline triples (no
// data file ships, owner 2026-10-20) and the store answers a query.

import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { sampleStorePath, sampleStoreFacts } from '../sample-store.mjs';
import * as f from '../index.mjs';

test('sampleStorePath packs a store and openStore answers its triple count', async () => {
  const dir = join(mkdtempSync(join(tmpdir(), 'factoidal-ss-test-')), 'store');
  try {
    assert.equal(sampleStorePath(dir), dir);
    assert.ok(existsSync(join(dir, 'CURRENT')));
    assert.equal(sampleStorePath(dir), dir, 'a second call reuses the store');
    const store = await f.openStore(dir);
    const n = await store.query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
    assert.equal(Number(n[0].get('n').value), sampleStoreFacts.triples);
    await store.close();
    assert.equal(f.sampleStorePath, sampleStorePath);
  } finally {
    rmSync(join(dir, '..'), { recursive: true, force: true });
  }
});
