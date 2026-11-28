#!/usr/bin/env node
/** Test-only ordered commitment oracle. Never import into the Lean runtime.
 * Reconstructs the dated reference roots; does not execute a block or attest
 * a header, state root, or a production EL/CL verdict.
 */
import { readFileSync } from 'node:fs';
import { RLP, MerklePatriciaTrie, bytes, hex, nat, fixed, keccak, digest } from './oracle.mjs';

async function audit(snapshot, { bytes, hex, nat, fixed, keccak, rlp, root }) {
  const require = (condition, description) => { if (!condition) throw Error(description) };
  const equal = (actual, expected, description) =>
    require(actual === expected, `${description}: ${actual} != ${expected}`);
  const concat = (a, b) => Uint8Array.from([...a, ...b]);
  function receiptBytes(rec) {
    require([0, 1, 2, 3].includes(rec.type), "unsupported fixture receipt kind");
    require([0, 1].includes(rec.receiptStatus), "invalid fixture receipt status");
    const bloom = new Uint8Array(256);
    const logs = rec.logs.map(log => {
      const address = fixed(log.address, 20);
      const topics = log.topics.map(topic => fixed(topic, 32));
      for (const value of [address, ...topics]) {
        const h = keccak(value);
        for (let j = 0; j < 6; j += 2) {
          const bit = (h[j] * 256 + h[j + 1]) & 2047;
          bloom[255 - (bit >> 3)] |= 1 << (bit % 8);
        }
      }
      return [address, topics, bytes(log.dataHex)];
    });
    const body = rlp([nat(rec.receiptStatus), nat(rec.cumulativeGasUsed), bloom, logs]);
    return rec.type === 0 ? body : concat(Uint8Array.of(rec.type), body);
  }
  equal(hex(keccak(new Uint8Array())), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470", "empty Keccak");
  equal(hex(keccak(Uint8Array.of(97, 98, 99))), "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45", "abc Keccak");
  equal(await root([]), "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421", "empty ordered trie");
  equal(snapshot.rows.length, 36, "fixture inventory");
  equal(snapshot.rows.reduce((n, row) => n + row.txBytes.length, 0), 344, "signed occurrence inventory");
  const counts = { transactionRoots: 0, receiptRoots: 0, executedSignedOccurrences: 0,
    receiptEncodings: 0, omission: 0, order: 0, byteMutation: 0, receiptStatus: 0,
    receiptGas: 0, receiptLog: 0, withoutExpectedRoots: 0, types: {} };
  const rows = [];
  const changed = async (values, original, label, field) => {
    require(await root(values) !== original, label);
    counts[field]++;
  };
  for (const row of snapshot.rows) {
    if (row.category !== "execution") {
      require(row.transactionRoot == null && row.receiptsRoot == null, `${row.id}: unexpected roots on refusal`);
      counts.withoutExpectedRoots++;
      continue;
    }
    const tx = row.txBytes.map(bytes);
    const receipts = row.receipts.map(receiptBytes);
    equal(receipts.length, tx.length, `${row.id}: receipt inventory`);
    const txRoot = await root(tx);
    const receiptsRoot = await root(receipts);
    equal(txRoot, hex(bytes(row.transactionRoot)), `${row.id}: ordered transaction root`);
    equal(receiptsRoot, hex(bytes(row.receiptsRoot)), `${row.id}: ordered receipt root`);
    counts.transactionRoots++;
    counts.receiptRoots++;
    counts.executedSignedOccurrences += tx.length;
    counts.receiptEncodings += receipts.length;
    for (const rec of row.receipts) counts.types[rec.type] = (counts.types[rec.type] || 0) + 1;
    if (tx.length) {
      await changed(tx.slice(1), txRoot, `${row.id}: omission`, "omission");
      const mutated = tx.map(value => value.slice());
      mutated[0][mutated[0].length - 1] ^= 1;
      await changed(mutated, txRoot, `${row.id}: raw byte mutation`, "byteMutation");
    }
    if (tx.length > 1 && hex(tx[0]) !== hex(tx[1])) {
      await changed([tx[1], tx[0], ...tx.slice(2)], txRoot, `${row.id}: reordering`, "order");
    }
    if (receipts.length) {
      const first = row.receipts[0];
      const mutate = (rec, label, field) =>
        changed([receiptBytes(rec), ...receipts.slice(1)], receiptsRoot, `${row.id}: ${label}`, field);
      await mutate({ ...first, receiptStatus: 1 - first.receiptStatus }, "receipt status", "receiptStatus");
      await mutate({ ...first, cumulativeGasUsed: String(BigInt(first.cumulativeGasUsed) + 1n) },
        "cumulative gas", "receiptGas");
      if (first.logs.length) {
        const log = { ...first.logs[0], dataHex: first.logs[0].dataHex + "00" };
        await mutate({ ...first, logs: [log, ...first.logs.slice(1)] }, "log bytes", "receiptLog");
      }
    }
    rows.push({ id: row.id, transactionRoot: txRoot, receiptsRoot, receiptBytesHex: receipts.map(hex) });
  }
  const expected = { transactionRoots: 30, receiptRoots: 30, executedSignedOccurrences: 327,
    receiptEncodings: 327, omission: 29, order: 28, byteMutation: 29, receiptStatus: 29,
    receiptGas: 29, receiptLog: 9, withoutExpectedRoots: 6 };
  for (const [key, value] of Object.entries(expected)) equal(counts[key], value, key);
  for (const [kind, value] of [[0, 6], [1, 3], [2, 293], [3, 25]]) equal(counts.types[kind], value, `kind ${kind}`);
  return { counts, rows };
}

async function comparatorControls(snapshot, oracle) {
  let count = 0;
  for (const [key, label] of [["transactionRoot", "ordered transaction root"], ["receiptsRoot", "ordered receipt root"]]) {
    const altered = JSON.parse(JSON.stringify(snapshot));
    altered.rows[0][key] = "0x" + "00".repeat(32);
    let refused = false;
    try { await audit(altered, oracle); } catch (e) { refused = String(e).includes(label); }
    if (!refused) throw Error("comparator accepted altered " + key);
    count++;
  }
  return count;
}

const snapshotBytes = readFileSync(new URL('../../evidence/2026-11-24-transaction-list/list-execution.json', import.meta.url));
if (digest(snapshotBytes) !== 'ff3e56deaec8c8ff4cb99725f8d8283565a0e0fcf1c4fed175596faba5a3f484') {
  throw Error('dated reference evidence pin');
}
async function orderedRoot(values) {
  // Transaction and receipt tries use RLP(index), not Keccak(index).
  const trie = new MerklePatriciaTrie({ useKeyHashing: false });
  for (let i = 0; i < values.length; i++) await trie.put(RLP.encode(nat(i)), values[i]);
  return hex(trie.root());
}
const oracle = { bytes, hex, nat, fixed, keccak, rlp: value => RLP.encode(value), root: orderedRoot };
const args = process.argv.slice(2);
if (args.length > 1 || (args.length && args[0] !== '--emit-fixtures')) throw Error('usage: check-ordered-commitments.mjs [--emit-fixtures]');
const snapshot = JSON.parse(snapshotBytes);
const report = await audit(snapshot, oracle);
console.log(JSON.stringify({ scope: 'test-only dated root reconstruction, not block execution',
  counts: report.counts, comparatorControls: await comparatorControls(snapshot, oracle),
  ...(args.length ? { rows: report.rows } : {}) }, null, 2));
