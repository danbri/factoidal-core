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

// Issue 843 (https://github.com/danbri/factoidal/issues/843). Only a torn
// final record (an append that did not complete) is left out of the merge. A
// damaged record with records after it, and a record whose checksum verifies
// but whose entries the engine cannot decode, make the merge and the
// inspection reject: before 2026-10-14 the merge applied the records before
// such a record and lost it and every later record without a message.
const u32 = (n) => [n & 255, (n >>> 8) & 255, (n >>> 16) & 255, (n >>> 24) & 255];
const u64 = (n) => [...u32(n), 0, 0, 0, 0];
const byteSum = (bytes) => bytes.reduce((a, b) => (a + b) >>> 0, 0);
const frameOf = (magic, body) => [...magic, ...u32(1), ...u32(body.length), ...body, ...u32(byteSum(body))];
const hexOf = (bytes) => bytes.map((b) => b.toString(16).padStart(2, '0')).join('');
// One DLB1 record, seq 9, whose one DLE1 entry has the unknown entry tag 9.
const undecodableRecord = hexOf(frameOf([0x44, 0x4c, 0x42, 0x31],
  [...u64(9), ...u64(0), ...u32(1), ...frameOf([0x44, 0x4c, 0x45, 0x31], [9])]));
// Add 1 to the hex digit at `i` (a body byte when i >= 24): the checksum fails.
const bumpHex = (hex, i) =>
  hex.slice(0, i) + ((parseInt(hex[i], 16) + 1) % 16).toString(16) + hex.slice(i + 1);

test('deltaLog: a torn final record recovers; damaged and undecodable records reject (issue 843)', async () => {
  const records = [];
  const store = {
    async open() {},
    async append(name, makeRecord) {
      const seq = records.length;
      records.push(makeRecord(seq).hex);
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
  const h = await api.deltaLogOpen('issue-843');
  await api.deltaLogAppend(h, ins('a', '1'));
  await api.deltaLogAppend(h, ins('b', '2'));
  const [r0, r1] = records.slice();
  const use = (...recs) => { records.splice(0, records.length, ...recs); };
  // Torn: the last record cut by 4 bytes, or complete with one body byte changed.
  for (const last of [r1.slice(0, -8), bumpHex(r1, 50)]) {
    use(r0, last);
    const merged = await api.deltaLogMerge(h, '');
    assert.match(merged, /"1"/);
    assert.doesNotMatch(merged, /"2"/);
    const info = await api.deltaLogInspect(h);
    assert.deepEqual([info.batches, info.torn, info.tornBytes], [1, true, last.length / 2]);
  }
  // Damaged: the first record with one body byte changed, a record after it.
  use(bumpHex(r0, 50), r1);
  await assert.rejects(api.deltaLogMerge(h, ''), /damaged frame at byte 0/);
  await assert.rejects(api.deltaLogInspect(h), /damaged frame at byte 0/);
  // Undecodable: at the end, and in the middle of the log.
  use(r0, r1, undecodableRecord);
  await assert.rejects(api.deltaLogMerge(h, ''), /cannot decode/);
  await assert.rejects(api.deltaLogInspect(h), /cannot decode/);
  use(r0, undecodableRecord, r1);
  await assert.rejects(api.deltaLogMerge(h, ''), /cannot decode/);
  // The clean log merges again.
  use(r0, r1);
  assert.match(await api.deltaLogMerge(h, ''), /"2"/);
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
