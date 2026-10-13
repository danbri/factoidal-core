// The durable update log (deltaLog*, hub post 18,
// https://github.com/danbri/factoidal/issues/728) on both Node entries.
//
// The engine ops deltaLogEncode / deltaLogDecode / deltaLogMerge
// (formal/lean4/Wasm/Ops/DeltaLog.lean) make every byte decision; these
// cases check the package layer: handles, seq allocation by the host store,
// the result shapes, refusals, and that a host store sees only the engine's
// hexadecimal records. The IndexedDB store runs in a browser only; it is
// checked by tests/web-demos/hub_browser_all.sh (hub post 18).

import test from 'node:test';
import assert from 'node:assert/strict';
import * as full from '../index.mjs';
import * as core from '../core.mjs';
import { buildApi } from '../lib/api.mjs';
import { entryFromEngine } from '../lib/lean-entry.mjs';

const ins = (s, o) => `INSERT DATA { <http://example.org/${s}> <http://example.org/p> "${o}" . }`;

for (const [label, api] of [['full', full], ['core', core]]) {
  test(`deltaLog (${label}): append, read, merge, inspect, torn last record`, async () => {
    const h = await api.deltaLogOpen(`delta-log-test-${label}`);
    await api.deltaLogDestroy(h);
    assert.deepEqual(await api.deltaLogAppend(h, ins('a', '1')), { seq: 0, opCount: 1 });
    assert.deepEqual(await api.deltaLogAppend(h,
      `${ins('b', '2')} ; DELETE DATA { <http://example.org/a> <http://example.org/p> "1" . }`),
    { seq: 1, opCount: 2 });
    const hex = (await api.deltaLogReadAllHex(h)).split('\n');
    assert.equal(hex.length, 2);
    let merged = await api.deltaLogMerge(h, '');
    assert.match(merged, /"2"/);
    assert.doesNotMatch(merged, /"1"/);
    let info = await api.deltaLogInspect(h);
    assert.deepEqual([info.batches, info.entries, info.torn, info.tornBytes],
      [2, 3, false, 0]);
    assert.equal(info.logBytes, (hex[0].length + hex[1].length) / 2);
    assert.equal(await api._deltaLogCorruptLastForTest(h), true);
    info = await api.deltaLogInspect(h);
    assert.deepEqual([info.batches, info.torn, info.tornBytes], [1, true, hex[1].length / 2 - 4]);
    merged = await api.deltaLogMerge(h, '');
    assert.match(merged, /"1"/);
    assert.doesNotMatch(merged, /"2"/);
    await api.deltaLogDestroy(h);
    assert.equal(await api.deltaLogReadAllHex(h), '');
    assert.equal(await api._deltaLogCorruptLastForTest(h), false);
    assert.equal((await api.capabilities()).deltaLog, true);
  });
}

test('deltaLog: the default log name, and refusals', async () => {
  const h = await full.deltaLogOpen();
  assert.equal(h.dbName, 'factoidal-delta-log');
  await assert.rejects(full.deltaLogAppend(h, 'LOAD <http://example.org/x>'),
    /admits INSERT DATA/);
  await assert.rejects(full.deltaLogAppend(h, 'INSERT DATA {'), /parse error/);
  assert.equal(await full.deltaLogReadAllHex(h), '');
  await assert.rejects(full.deltaLogAppend(null, ins('a', '1')), TypeError);
  await assert.rejects(full.deltaLogAppend(h, 42), TypeError);
  await assert.rejects(full.deltaLogAppend(h, ins('a', '1'), { epoch: -1 }), TypeError);
  await assert.rejects(full.deltaLogMerge(h, null), TypeError);
  await assert.rejects(full.deltaLogMerge(h, 'not n-quads'), /deltaLogMerge/);
});

test('deltaLog: a host store receives the engine record and the seq it allocates', async () => {
  const seen = [];
  const records = [];
  const store = {
    async open() {},
    async append(name, makeRecord) {
      const seq = 40 + records.length; // the store, not the package, allocates seq
      const rec = makeRecord(seq);
      seen.push({ name, seq, rec });
      records.push(rec.hex);
      return { seq };
    },
    async readAll() { return records.slice(); },
    async destroy() { records.length = 0; },
    async corruptLast() { return false; },
  };
  const api = buildApi({
    engineName: 'test',
    loadEntry: async () => entryFromEngine(await full.loadEngine()),
    deltaLogStore: store,
  });
  const h = await api.deltaLogOpen('custom');
  const r = await api.deltaLogAppend(h, ins('c', '3'), { epoch: 7 });
  assert.deepEqual(r, { seq: 40, opCount: 1 });
  assert.equal(seen.length, 1);
  assert.equal(seen[0].rec.epoch, 7);
  assert.match(seen[0].rec.hex, /^444c4231[0-9a-f]+$/); // 'DLB1', little-endian
  const info = await api.deltaLogInspect(h);
  assert.deepEqual(info.records, [{ seq: 40, epoch: 7, entries: 1 }]);
  // A refused update calls the store's append but throws from makeRecord: the
  // store gets no record.
  await assert.rejects(api.deltaLogAppend(h, 'CLEAR ALL'), /admits INSERT DATA/);
  assert.equal(records.length, 1);
});
